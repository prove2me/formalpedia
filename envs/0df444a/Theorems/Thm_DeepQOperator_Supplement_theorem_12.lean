-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_12
-- name    : DeepQOperator.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:45:55.417036+00:00
-- url     : https://prove2.me/theorems/139ba05a-98b5-4439-ac1e-91da700d3954
-- title:
--   Theorem 12, p.44 — adaptive decision separation for the normalized family
-- statement:
--   For the normalized Bellman family (76)–(78) on $P_m=[0,m+1]\times[0,1]^m$, $m\ge2$, $0<\gamma<1$:
--
--   1. Two adaptive raw critic queries suffice to return a zero-regret decision on every parameter.
--   2. Every deterministic procedure that uses at most $m$ fixed affine measurements of $\theta$ has worst-case regret at least $\gamma/(16m)$. Consequently the fixed exact-decision query complexity is $m+1$, while the adaptive affine-query and adaptive raw-query complexities are both $2$.
--   3. For the raw oracle, the deterministic minimax curves (4) are
--   $$
--   \mathfrak D^{\mathrm{fixed,raw}}_N=\begin{cases}\gamma/(2m),&0\le N\le m,\\0,&N\ge m+1,\end{cases}\qquad \mathfrak D^{\mathrm{adaptive,raw}}_N=\begin{cases}\gamma/(2m),&N=0,1,\\0,&N\ge2.\end{cases} \tag{79}
--   $$
--
--   Adaptivity here removes the dependence on $m$ entirely: two adaptive queries are exact, while every fixed design needs $m+1$.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - reading: the minimax value is at most $x$ (an upper bound on an infimum) → there is an algorithm of the class whose worst regret is at most $x$; reason: the source proves each upper bound by an explicit algorithm or design it describes
--   - encoding: deterministic minimax value $\mathfrak D_N=x$ → every deterministic algorithm of the class has worst regret $\ge x$, and one attains $\le x$ (or $=0$); reason: an infimum equals $x$ when it is a lower bound and attained
--   - reading: fixed exact-decision complexity $m+1$; adaptive affine and raw complexities $2$ → a deterministic design with $m+1$ rows is exact; part 2 excludes $\le m$ rows; a two-query raw algorithm is exact and every deterministic one-query affine algorithm has positive worst regret; reason: exact complexity is two-sided
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 12 and eq. (79), p.44 (PDF p.47); family (76)–(78), p.43

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Normalized

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 12 (Adaptive decision separation)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive
Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256 9f8f3285…),
Theorem 12, p.44, PDF p.47).

For the normalized family (76)–(78), `m ≥ 2`, `0 < γ < 1`:
1. two adaptive raw critic queries return a zero-regret decision on every parameter of `P_m`;
2. every deterministic procedure using at most `m` fixed affine measurements has worst-case regret at
   least `γ/(16m)`; consequently the exact-decision query complexity is `m + 1` for fixed affine
   information, and `2` for adaptive affine and for adaptive raw information;
3. the deterministic raw minimax curves (79) are `𝔇^{fixed,raw}_N = γ/(2m)` for `0 ≤ N ≤ m` and `0` for
   `N ≥ m + 1`, and `𝔇^{adaptive,raw}_N = γ/(2m)` for `N = 0, 1` and `0` for `N ≥ 2`.

**Formalization Note.** Deterministic procedures have the one-point seed space `Unit` with the Dirac
measure, so `designRegret`/`algRegret` are `sup_θ ℓ(A(θ), θ)` as in (4). A fixed procedure is an
`ExactDesign` with `N` rows (at most `N` measurements: a repeated or zero row carries no new
information); "raw" is `IsRawDesign (nDictionary m)` resp. `IsRaw (nDictionary m)`. An adaptive
procedure is an `AdaptiveAlg` with exact replies run with fuel `N`. No measurability is imposed on
deterministic procedures (the class of (4)). Each minimax value `inf_A sup_θ ℓ = v` is stated as a lower
bound `v` for every procedure of the class together with a procedure of the class attaining `v`. -/
theorem theorem_12 :
    ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      -- 1. two adaptive raw queries are exact
      (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧
        algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A 2 = 0) ∧
      -- 2. at most `m` fixed affine measurements: worst-case regret at least `γ/(16m)`
      (∀ N : ℕ, N ≤ m → ∀ D : ExactDesign (NCoord m) Unit N,
        ENNReal.ofReal (γ / (16 * m)) ≤ designRegret (nBox m) (nLoss m γ) (Measure.dirac ()) D) ∧
      -- fixed exact-decision complexity `m + 1`
      (∃ D : ExactDesign (NCoord m) Unit (m + 1),
        designRegret (nBox m) (nLoss m γ) (Measure.dirac ()) D = 0) ∧
      -- adaptive affine (hence raw) complexity `2`: one adaptive affine query is not exact
      (∀ A : AdaptiveAlg (NCoord m) Unit, A.IsExact →
        0 < algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A 1) ∧
      -- 3. the deterministic fixed raw curve (79)
      (∀ N : ℕ, N ≤ m →
        (∀ D : ExactDesign (NCoord m) Unit N, IsRawDesign (nDictionary m) D →
          ENNReal.ofReal (γ / (2 * m)) ≤ designRegret (nBox m) (nLoss m γ) (Measure.dirac ()) D) ∧
        (∃ D : ExactDesign (NCoord m) Unit N, IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) (Measure.dirac ()) D ≤ ENNReal.ofReal (γ / (2 * m)))) ∧
      (∀ N : ℕ, m + 1 ≤ N →
        ∃ D : ExactDesign (NCoord m) Unit N, IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) (Measure.dirac ()) D = 0) ∧
      -- the deterministic adaptive raw curve (79)
      (∀ N : ℕ, N ≤ 1 →
        (∀ A : AdaptiveAlg (NCoord m) Unit, A.IsExact → A.IsRaw (nDictionary m) →
          ENNReal.ofReal (γ / (2 * m)) ≤ algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N) ∧
        (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧
          algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N ≤ ENNReal.ofReal (γ / (2 * m)))) ∧
      (∀ N : ℕ, 2 ≤ N →
        ∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧
          algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A N = 0) := by sorry

end DeepQOperator.Supplement
