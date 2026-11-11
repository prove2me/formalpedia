-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_lemma_3_1
-- name    : ForestRoundingNSW.Rounding.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:51:32.577251+00:00
-- url     : https://prove2.me/theorems/6db01c6a-a3f2-48c6-8dd4-02daf41df3c0
-- title:
--   Lemma 3.1 ([CKMV26, Thm 4]) — cycle elimination: forest support, no multilinear value lost, no new edge, polynomially many operations
-- statement:
--   Let $f_1,\dots,f_n$ be normalized monotone submodular functions on the items with multilinear extensions $F_{f_i}$, and let $x\in P$. Under the exact-evaluation convention, one can compute a feasible fractional allocation $y\in P$ with
--
--   (3.1a) the support graph of $y$ is a forest;
--
--   (3.1b) $F_{f_i}(y_i)\ge F_{f_i}(x_i)$ for every agent $i$;
--
--   (3.1c) no new positive support edge: $y_{ij}>0\Rightarrow x_{ij}>0$.
--
--   The procedure uses polynomially many exact derivative evaluations, arithmetic operations and comparisons: there are a universal constant $C_0$ and one deterministic admissible program on the oracle real RAM that, on every instance, halts within $C_0(n+m)^{C_0}+C_0$ steps with such a $y$ as its output.
--
--   This is the cycle-cancellation theorem of Chekuri, Kulkarni, Mehta and Vondrák, used as the first step of Proposition 3.4.
--
--   Differences from the source:
--   - reading: one can compute … using polynomially many exact derivative evaluations, arithmetic operations, and comparisons → ∃ universal C0 ∃ one admissible program without uniform draws: on every instance (and every tape) it halts within C0·(n+m)^C0 + C0 steps with output y satisfying (3.1a)–(3.1c); reason: the paper's deterministic algorithm model with exact oracles
--   - encoding: f_i : 2^M → ℝ≥0 normalized monotone submodular, x ∈ P → f_i : Finset (Fin m) → ℝ with IsNMS, x with nonnegative entries and item totals ≤ 1; the program's input has G = all items and no kept bundles; reason: nonnegativity follows; x ∈ P with totals ≤ 1 as the paper states (its remark after the lemma)
--   - encoding: the computed allocation y → the real output block of the halted run; reason: the machine's output convention
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 19, Lemma 3.1

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions
import Definitions.Def_ForestRoundingNSW_Rounding_Allocation
import Definitions.Def_ForestRoundingNSW_Rounding_Machine

open NonmonotoneSubmod.Shared

namespace ForestRoundingNSW.Rounding

theorem lemma_3_1 :
    ∃ C0 : ℕ, ∃ P : Program, Admissible P ∧ NoUnif P ∧
      ∀ (n m : ℕ) (x : Fin n → Fin m → ℝ) (f : Fin n → Finset (Fin m) → ℝ),
        InP x → (∀ i, IsNMS (f i)) → ∀ ν : Tape,
          HaltsWithin P f ν (initState n m x Finset.univ (fun _ => ∅)) (C0 * (n + m) ^ C0 + C0) ∧
          InP (outMatrix P f (initState n m x Finset.univ (fun _ => ∅)) ν) ∧
          IsForest (outMatrix P f (initState n m x Finset.univ (fun _ => ∅)) ν) ∧
          (∀ i : Fin n, F (f i) (x i) ≤
            F (f i) (outMatrix P f (initState n m x Finset.univ (fun _ => ∅)) ν i)) ∧
          ∀ (i : Fin n) (j : Fin m),
            0 < outMatrix P f (initState n m x Finset.univ (fun _ => ∅)) ν i j → 0 < x i j := by sorry

end ForestRoundingNSW.Rounding
