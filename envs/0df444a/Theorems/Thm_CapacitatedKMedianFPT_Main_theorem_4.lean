-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_theorem_4
-- name    : CapacitatedKMedianFPT.Main.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:33.384531+00:00
-- url     : https://prove2.me/theorems/72ac8418-6339-4c36-b8e9-1d05ed303b58
-- title:
--   Theorem 4 — capacity-preserving submodular maximization over a partition
-- statement:
--   Let $F$ be a ground set of $n$ elements, $v:2^F\to\mathbb Q_{\ge0}$ a monotone submodular function with $v(\emptyset)=0$ accessed through a value oracle, $U_f\in\mathbb Z_{\ge0}$ a capacity for each $f\in F$, and $F_1,\dots,F_k$ a partition of $F$. There is a deterministic FPT algorithm that outputs subsets $S_1,\dots,S_\tau$ of $F$ such that
--
--   1. for each $j\in[\tau]$ and $i\in[k]$, $S_j\cap F_i$ has exactly one element $s^i_j$;
--   2. for every choice $O=\{o_1,\dots,o_k\}$ with $o_i\in F_i$ there is $j\in[\tau]$ with
--   $$v(S_j)\ge\Bigl(1-\frac1e-\varepsilon\Bigr)v(O)\quad\text{and}\quad U_{s^i_j}\ge U_{o_i}\ \text{for each }i\in[k].$$
--
--   Moreover $\tau\le n(k/\varepsilon)^{O(k^2/\varepsilon)}$, and the number of oracle calls and the running time are both at most $n^2(k/\varepsilon)^{O(k^2/\varepsilon)}$.
--
--   The output family does not depend on $O$: one family serves every comparator, with simultaneous domination of the capacities in every part. Here $0<\varepsilon<1/2$ (the paper's standing assumption).
--
--   **Formalization Note** The program receives $n,k,\varepsilon$, the part index and capacity of each element, and queries $v$ through the oracle instruction. Time is unit cost (an oracle call reading $\ell$ cells costs $1+\ell$). All three $O(k^2/\varepsilon)$ exponents use one absolute constant $c$ chosen first.
--
--   Differences from the source:
--
--   - encoding: value oracle model, number of oracle calls and running time → a program of `Machine` with the query instruction; unit-cost time and the count of oracle calls; reason: unit-cost arithmetic and unit-cost oracle calls are the conventions of the value-oracle model; the values of v have no size bound
--   - generalization: a deterministic FPT algorithm for the fixed error parameter ε → one program receiving ε ∈ (0, 1/2) ∩ ℚ as input; reason: hard-coding ε recovers an algorithm for each fixed ε
--   - encoding: a ground set on n elements partitioned into k subsets → F = {0, …, n−1} with n ≥ 1, part indices in [k] (parts may be empty), k ≥ 1; reason: for n = 0 the bound n²·(k/ε)^… = 0 cannot be met by a halting program; k ≥ 1 is the source's setting
--   - encoding: O(k²/ε) in the three bounds → one absolute constant c, exponent c·k²/ε; reason: the meaning of O with a universal constant; k/ε > 2
--   - encoding: the collection S_1, …, S_τ with S_j ∩ F_i = {s^i_j} → a table of the elements s^i_j with s^i_j ∈ F_i; reason: S_j = {s^1_j, …, s^k_j}; disjointness of the parts gives exactly one element per part
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 13, Theorem 4 (restated p. 15); proof p. 15–19, Algorithms 2–4; p. 5, the error parameter 0 < ε < 1/2

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Machine
import Definitions.Def_CapacitatedKMedianFPT_Main_Encoding
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_SubsamplingSM_Offline_IsMonotoneSetFn

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Theorem 4** (p. 13, proof p. 15–19). One deterministic oracle program `A` and one absolute
constant `c`: for every ground set `[n]` (`n ≥ 1`), partition into `k ≥ 1` parts, capacities `U`,
`0 < ε < 1/2` and normalized monotone submodular `v : 2^{[n]} → ℚ≥0` given by a value oracle, `A`
outputs transversals `S_1, …, S_τ` (`s_j^i ∈ F_i`), with `τ ≤ n (k/ε)^{ck²/ε}`, such that for every
transversal `O = {o_1, …, o_k}` some `S_j` has `v(S_j) ≥ (1 − 1/e − ε) v(O)` and `U_{s_j^i} ≥ U_{o_i}`
for all `i`; oracle calls and unit-cost time are at most `n² (k/ε)^{ck²/ε}`. -/
theorem theorem_4 :
    ∃ (A : Program) (c : ℕ), ∀ (n k : ℕ) (ε : ℚ) (part : Fin n → Fin k) (U : Fin n → ℕ)
      (v : Finset (Fin n) → ℚ),
      1 ≤ n → 1 ≤ k → 0 < ε → ε < 1 / 2 → v ∅ = 0 → (∀ S, 0 ≤ v S) →
      SubsamplingSM.Offline.IsMonotoneSetFn (fun S => (v S : ℝ)) →
      NonmonotoneSubmod.Shared.Submodular (fun S => (v S : ℝ)) →
      ∃ (mem : Memory) (s : Stats), RunsTo A (setOracle n v) (submodInput n k ε part U) mem s ∧
        (s.unitTime : ℝ) ≤ (n : ℝ) ^ 2 * ((k : ℝ) / ε) ^ ((c : ℝ) * k ^ 2 / ε) ∧
        (s.queries : ℝ) ≤ (n : ℝ) ^ 2 * ((k : ℝ) / ε) ^ ((c : ℝ) * k ^ 2 / ε) ∧
        ∃ (τ : ℕ) (sel : Fin τ → Fin k → Fin n), IsTransversalFamilyOutput n k mem τ sel ∧
          (τ : ℝ) ≤ (n : ℝ) * ((k : ℝ) / ε) ^ ((c : ℝ) * k ^ 2 / ε) ∧
          (∀ j i, part (sel j i) = i) ∧
          ∀ o : Fin k → Fin n, (∀ i, part (o i) = i) →
            ∃ j : Fin τ,
              (1 - 1 / Real.exp 1 - (ε : ℝ)) * (v (Finset.univ.image o) : ℝ) ≤
                (v (Finset.univ.image (sel j)) : ℝ) ∧
              ∀ i, U (o i) ≤ U (sel j i) := by sorry

end CapacitatedKMedianFPT.Main
