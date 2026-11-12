-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_corollary_4_7
-- name    : FasterWCTFPTAS.Main.corollary_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:58.775331+00:00
-- url     : https://prove2.me/theorems/0aea8b7b-56d6-4478-9da4-5517fd7ccc41
-- title:
--   Corollary 4.7 — δ-representative sets of size O(1/δ^{(m−1)/2}) in time O(|D| log 1/δ + 1/δ^{(m−1)/2+α}); for m = 2 size O(1/√δ), time O(|D| + 1/√δ)
-- statement:
--   Fix $m\ge2$ machines.
--
--   1. For every constant $\alpha>0$ there are an admissible program and a constant $C>0$ such that for every sorted instance with $p_j>0$, $w_j\ge0$, every $i\in[n]$, every $\delta\in(0,1)$ and every list of $N$ pairs $D\subseteq\mathrm{DP}_i$, the program run on $(\delta,T_i,U_i,W_{>i},D)$ halts within
--   $$
--   C\Big(N\big(1+\log_2\tfrac1\delta\big)+\frac1{\delta^{(m-1)/2+\alpha}}\Big)
--   $$
--   steps and outputs the indices of at most $C/\delta^{(m-1)/2}$ pairs of $D$ forming a $\delta$-representative set of $D$ for $i$.
--   2. If $m=2$, there are an admissible program and a constant $C>0$ doing the same with at most $C/\sqrt\delta$ output pairs within $C(N+1/\sqrt\delta)$ steps.
--
--   This is the sparsification step of the FPTAS (Line 1.5 of Algorithm 1).
--
--   **Formalization Note** Each program and its constant are fixed before the instance and depend only on $m$ (and $\alpha$). The program receives $\delta$, the three prefix quantities $T_i,U_i,W_{>i}$ and the pairs, not the instance itself: the running time $O(|D|\log1/\delta+\dots)$ excludes reading the instance, and the FPTAS precomputes these prefix sums once.
--
--   Differences from the source:
--   - reading: running time in O(·), machine model not named → number of executed instructions of an admissible program of the deterministic unit-cost real RAM of FasterWCTFPTAS.Main.Machine (rational literals, exact + − × ÷, comparisons, indirect addressing, work-bounded floor); reason: the source names no machine; this model supports the cited real-arithmetic constructions and excludes bit tricks that would trivialize the bound
--   - reading: O(·) bounds with a fixed constant → ∃ C > 0 chosen together with the program, before the instance, i, δ and D; it may depend only on the fixed m and α; reason: standard meaning of O(·) for a fixed dimension and constant α
--   - reading: log(1/δ) in the time bound → 1 + log₂(1/δ); reason: the O(·) bound is asymptotic as δ → 0; read literally, N·log(1/δ) tends to 0 as δ → 1 and falls below the N steps needed to read the input; logarithms are base 2 (p. 1)
--   - reading: "given i ∈ [n], δ ∈ (0, 1), and D ⊆ DP_i, we can compute" → the program's input is (δ, T_i, U_i, W_{>i}, D); the conclusion holds for every instance, every i and every D ⊆ DP_i; reason: the stated time does not allow reading the instance; T_i, U_i and W_{>i} are what Lemma 4.6 needs, and the FPTAS computes them by prefix sums
--   - encoding: a set of N pairs → a list Fin N → ℝ^{m−1} × ℝ of N pairs (repetitions allowed), written as its coordinates; the output is a list of indices into it and the size is the list length; reason: a set of N distinct points is a list without repetitions; the list length bounds the number of selected points
--   - reading: Definition 4.2: for every pair (π^S, θ^S) ∈ D there exists (π^S̃, θ^S̃) ∈ D̃ with cost(S̃ ∪ S′) ≤ cost(S ∪ S′) + δOPT → for every schedule S whose pair lies in D there is a schedule S̃ whose pair lies in D̃ with that inequality; reason: cost(S ∪ S′) depends on S only through (π^S, θ^S) (identity in the proof of Lemma 4.6), so both readings define the same notion
--   - encoding: OPT ≔ min over partitions processed in increasing index order of the sorted instance → OPT m p w, the minimum over all nonpreemptive schedules (assignment and any per-machine order); reason: on a sorted instance (a hypothesis here) the two minima coincide by Smith's rule, which §4 invokes
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 15 (PDF p. 16), Corollary 4.7

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Machine
import Definitions.Def_FasterWCTFPTAS_Main_Encoding
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Corollary 4.7, p. 15 (PDF 16). Fix `m ≥ 2`.
(1) For every constant `α > 0` there are an admissible program and `C > 0` such that for every
instance (`p_j > 0`, sorted by Smith's ratio), every `i ∈ [n]`, every `δ ∈ (0, 1)` and every list of
`N` pairs `D ⊆ DP_i`, the program run on `(δ, T_i, U_i, W_{>i}, D)` outputs a `δ`-representative set
of `D` for `i` of size at most `C/δ^{(m−1)/2}` within `C (N (1 + log₂(1/δ)) + 1/δ^{(m−1)/2+α})`
steps.
(2) If `m = 2`, there are an admissible program and `C > 0` doing the same with size at most `C/√δ`
within `C (N + 1/√δ)` steps. -/
theorem corollary_4_7 (m : ℕ) (hm : 2 ≤ m) :
    (∀ α : ℝ, 0 < α →
      ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (p w : Fin n → ℝ), (∀ j, 0 < p j) → (∀ j, 0 ≤ w j) → Sorted p w →
        ∀ (i : ℕ), 1 ≤ i → i ≤ n → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (N : ℕ) (pts : Fin N → Pt m), (∀ j, pts j ∈ DP m p w i) →
          ∃ idx : List (Fin N),
            Machine.output P (repInput δ (T p i) (U p w i) (Wgt w i) pts) =
              some (indexOutput idx) ∧
            Machine.HaltsWithin P (repInput δ (T p i) (U p w i) (Wgt w i) pts)
              (C * ((N : ℝ) * (1 + Real.logb 2 (1 / δ)) + (1 / δ) ^ (((m : ℝ) - 1) / 2 + α))) ∧
            (idx.length : ℝ) ≤ C * (1 / δ) ^ (((m : ℝ) - 1) / 2) ∧
            IsRepSet m p w i δ (idxSet pts idx) (Set.range pts)) ∧
    (m = 2 →
      ∃ P : Machine.Program, Machine.Admissible P ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (n : ℕ) (p w : Fin n → ℝ), (∀ j, 0 < p j) → (∀ j, 0 ≤ w j) → Sorted p w →
        ∀ (i : ℕ), 1 ≤ i → i ≤ n → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (N : ℕ) (pts : Fin N → Pt m), (∀ j, pts j ∈ DP m p w i) →
          ∃ idx : List (Fin N),
            Machine.output P (repInput δ (T p i) (U p w i) (Wgt w i) pts) =
              some (indexOutput idx) ∧
            Machine.HaltsWithin P (repInput δ (T p i) (U p w i) (Wgt w i) pts)
              (C * ((N : ℝ) + 1 / Real.sqrt δ)) ∧
            (idx.length : ℝ) ≤ C * (1 / Real.sqrt δ) ∧
            IsRepSet m p w i δ (idxSet pts idx) (Set.range pts)) := by sorry

end FasterWCTFPTAS.Main
