-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_14
-- name    : DeepQOperator.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:46:54.510028+00:00
-- url     : https://prove2.me/theorems/e9e49e7e-1edb-47c5-b82d-4d43e1f64363
-- title:
--   Theorem 14, p.45 — complete randomized raw-query curves for the normalized family
-- statement:
--   Let $c=\gamma/m$, $m\ge2$, $0<\gamma<1$. For the normalized family (76)–(78) on $P_m$,
--   $$
--   \mathfrak D^{\mathrm{fixed,raw,ran}}_N=\begin{cases}c/4,&N=0,1,\\ \frac c4\big(1-\frac{N-1}m\big),&2\le N\le m+1,\\0,&N>m+1,\end{cases}\qquad \mathfrak D^{\mathrm{adaptive,raw,ran}}_N=\begin{cases}c/4,&N=0,1,\\0,&N\ge2.\end{cases} \tag{81}
--   $$
--   The upper bounds hold on the whole continuous box $P_m$, and the lower bounds use finite distributions supported inside that box.
--
--   These are the exact randomized raw-query minimax values at every budget.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: the minimax value is at most $x$ (an upper bound on an infimum) → there is an algorithm of the class whose worst regret is at most $x$; reason: the source proves each upper bound by an explicit algorithm or design it describes
--   - encoding: the minimax value equals $x$ → every measurable algorithm of the class has worst regret $\ge x$, and one attains $\le x$ (or $=0$); reason: an infimum equals $x$ when it is a lower bound and attained; the paper's upper bounds are explicit algorithms (p.45)
--   - encoding: the lower bounds use finite distributions supported inside $P_m$ → lower bounds on the worst regret over $P_m$; reason: the sentence describes the proof; the statement is the values on $P_m$
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 14 and eq. (81), p.45 (PDF p.48); proof in Appendix P

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Normalized

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 14 (Complete randomized raw-query curves)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 14, p.45, PDF p.48; proved in Appendix P).

For the normalized family (76)–(78), `m ≥ 2`, `0 < γ < 1`, `c = γ/m`:
`𝔇^{fixed,raw,ran}_N = c/4` for `N = 0, 1`, `(c/4)(1 - (N-1)/m)` for `2 ≤ N ≤ m + 1`, `0` for `N > m + 1`
(81), and `𝔇^{adaptive,raw,ran}_N = c/4` for `N = 0, 1`, `0` for `N ≥ 2`. The upper bounds hold on the
entire continuous box `P_m`.

**Formalization Note.** The randomized fixed raw class is the measurable `ExactDesign (NCoord m) Ω N`
with every row in `nDictionary m`, on a standard Borel probability seed space; the randomized adaptive
raw class is the measurable `AdaptiveAlg` with exact replies and raw queries, run with fuel `N`. Each
value `inf_A sup_{θ ∈ P_m} E_ω ℓ = v` is stated as the lower bound `v` for every algorithm of the class
together with an algorithm of the class attaining `v` on all of `P_m`. `c = γ/m` is written out. -/
theorem theorem_14 :
    ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      -- the fixed randomized raw curve
      (∀ N : ℕ, N ≤ 1 →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable → IsRawDesign (nDictionary m) D →
          ENNReal.ofReal (γ / m / 4) ≤ designRegret (nBox m) (nLoss m γ) μ D) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D ≤ ENNReal.ofReal (γ / m / 4))) ∧
      (∀ N : ℕ, 2 ≤ N → N ≤ m + 1 →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable → IsRawDesign (nDictionary m) D →
          ENNReal.ofReal (γ / m / 4 * (1 - ((N : ℝ) - 1) / m)) ≤
            designRegret (nBox m) (nLoss m γ) μ D) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D ≤
            ENNReal.ofReal (γ / m / 4 * (1 - ((N : ℝ) - 1) / m)))) ∧
      (∀ N : ℕ, m + 1 < N →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D = 0) ∧
      -- the adaptive randomized raw curve
      (∀ N : ℕ, N ≤ 1 →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact → A.IsRaw (nDictionary m) → A.IsMeasurable →
          ENNReal.ofReal (γ / m / 4) ≤ algRegret (nBox m) (nLoss m γ) μ A N) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
          algRegret (nBox m) (nLoss m γ) μ A N ≤ ENNReal.ofReal (γ / m / 4))) ∧
      (∀ N : ℕ, 2 ≤ N →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (A : AdaptiveAlg (NCoord m) Ω),
          A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
          algRegret (nBox m) (nLoss m γ) μ A N = 0) := by sorry

end DeepQOperator.Supplement
