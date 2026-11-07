-- Prove2me | Theorems.Thm_ChoresEFX_theorem_4_1
-- name    : ChoresEFX.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:39.65056+00:00
-- url     : https://prove2.me/theorems/4deab86a-1e0b-4fe0-a4fd-62c53c827e6a
-- title:
--   Theorem 4.1 — BRBI runs in polynomial time and returns a complete $\alpha_B(m,n,k)$-EFkX allocation
-- statement:
--   For every well-formed instance and integer $k\ge1$, Algorithm 5 has a run, and every run returns a complete allocation that is $\alpha_B(m,n,k)$-EFkX, where
--
--   $$\alpha_B(m,n,k)=\max\left\{1,\frac{\lceil(m-kn)/n\rceil}{k}\right\}.$$
--
--   In particular:
--
--   1. $\alpha_B=1$ when $m\le2kn$;
--   2. $\alpha_B\le2-1/k$ when $m\le(3k-1)n$;
--   3. for $k=1$, the output is exactly EFX when $m\le2n$.
--
--   Moreover, one multi-stack Turing machine and one polynomial $P$ compute, for all such inputs, the output of a run within $P(n+m+|\mathrm{enc}|)$ steps.
--
--   The result gives exact fairness on sparse instances, and it is the branch of the main algorithm for $m\le2n$.
--
--   Differences from the source:
--   - reading: Algorithm 5 runs in polynomial time → one Turing machine and one polynomial P, with a run output within P(n + m + |enc|) steps; n, m and k are given in binary inside enc; reason: the paper names no machine (paper.md decisions 3-4); the same model as the goal
--   - reading: returns a complete allocation → a run exists and every run is a partition with the stated factor; all choices are universal; reason: the strongest reading of an algorithm with free choices (paper.md decision 8)
--   - generalization: n ≥ 2 (standing, p.5) → n ≥ 1; reason: Algorithm 5 and the bound make sense for one agent, and the statement specializes to n ≥ 2
--   - encoding: costs in ℚ≥0, chores and agents as sets → Fin n, Fin m, self-delimiting binary rationals, the allocation as a list of owners; malformed words are unconstrained; reason: a Lean convention; same instances
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Theorem 4.1, p.13

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ChoresEFX_Inst
import Definitions.Def_ChoresEFX_BrbiRun

namespace ChoresEFX

/-- **Theorem 4.1**, p.13.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

Algorithm 5 runs in polynomial time and returns a complete `α_B(m, n, k)`-EFkX allocation, where
`α_B(m, n, k) = max{1, ⌈(m − kn)/n⌉/k}`. In particular, exact EFkX when `m ≤ 2kn`, a factor of at most
`2 − 1/k` when `m ≤ (3k − 1)n`, and for `k = 1` exact EFX when `m ≤ 2n`.

**Formalization Note.** "Runs in polynomial time" is read on the multi-stack Turing machine of the goal:
one machine and one polynomial for all rational instances and all `k`, whose output is the output of a
run. The guarantee holds for every run, and a run exists. `(3k − 1)` is `ℕ`-subtraction at `k ≥ 1`, so it
does not truncate. -/
theorem theorem_4_1 :
    (∃ (M : Turing.TM2ComputableAux Bool Bool) (P : Polynomial ℕ),
      ∀ (I : Inst) (k : ℕ), I.WellFormed → 1 ≤ k →
        ∃ σ : Fin I.m → Fin I.n,
          BrbiRun I.realCost k (bundle σ) ∧
          HMBinPacking.OutputsWithin M (encBrbiInput I k) (encAlloc σ)
            (P.eval (I.n + I.m + (encBrbiInput I k).length))) ∧
    ∀ (I : Inst) (k : ℕ), I.WellFormed → 1 ≤ k →
      (∃ X, BrbiRun I.realCost k X) ∧
      (∀ X, BrbiRun I.realCost k X →
        IsPartition X ∧ IsAlphaEFkX I.realCost k (alphaB I.m I.n k) X) ∧
      (I.m ≤ 2 * k * I.n → alphaB I.m I.n k = 1) ∧
      (I.m ≤ (3 * k - 1) * I.n → alphaB I.m I.n k ≤ 2 - 1 / (k : ℝ)) ∧
      (k = 1 → I.m ≤ 2 * I.n → ∀ σ : Fin I.m → Fin I.n,
        BrbiRun I.realCost k (bundle σ) → IsAlphaEFX I.realCost 1 σ) := by sorry

end ChoresEFX
