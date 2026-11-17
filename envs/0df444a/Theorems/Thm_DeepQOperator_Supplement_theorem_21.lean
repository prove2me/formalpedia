-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_21
-- name    : DeepQOperator.Supplement.theorem_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:48:09.287498+00:00
-- url     : https://prove2.me/theorems/b4370b1b-53a3-4a8c-bfcc-fca7b6bfccfb
-- title:
--   Theorem 21, p.55 — the randomized affine regret rate $\gamma(m+1-N)/(192\pi^2m^2)$
-- statement:
--   For the normalized family (76)–(78), $m\ge2$, $0<\gamma<1$, and every integer $0\le N\le m$,
--   $$
--   \frac{\gamma(m+1-N)}{192\pi^2m^2}\ \le\ \mathfrak D^{\mathrm{fixed,aff,ran}}_N\ \le\ \frac{\gamma\min\{m,m+1-N\}}{4m^2}. \tag{91}
--   $$
--   Thus $\mathfrak D^{\mathrm{fixed,aff,ran}}_N=\Theta(\gamma(m+1-N)/m^2)$ with universal implicit constants. The upper bound uses only raw queries. For $N\ge m+1$ the value is zero. The exact randomized decision complexity is $m+1$ for fixed affine information and $2$ for adaptive affine or raw information. The lower bound allows arbitrary real measurement coefficients and measurable randomized decoders, without a processing-time restriction.
--
--   This is the second, isotropic-prior version of the rate of Theorem 13, with a different lower constant.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: the minimax value is at most $x$ (an upper bound on an infimum) → there is an algorithm of the class whose worst regret is at most $x$; reason: the source proves each upper bound by an explicit algorithm or design it describes
--   - reading: $\Theta(\gamma(m+1-N)/m^2)$ with universal implicit constants → absolute $c,C>0$ chosen before $m,\gamma,N$ with a lower bound for every design and an attaining design; reason: universal constants
--   - reading: exact randomized complexity $m+1$ fixed affine, $2$ adaptive affine or raw → a design with $m+1$ rows is exact and every measurable design with $\le m$ rows has positive worst regret; a deterministic two-query raw algorithm is exact and every measurable one-query affine algorithm has positive worst regret; reason: exact complexity is two-sided
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 21 and eq. (91), p.55 (PDF p.58); proof in Appendix N

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Normalized

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 21 (The randomized affine regret rate)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 21, p.55, PDF p.58; proved in Appendix N, pp.55–58).

For the normalized family (76)–(78), `m ≥ 2`, `0 < γ < 1`, and every integer `0 ≤ N ≤ m`,
`γ(m+1-N)/(192π²m²) ≤ 𝔇^{fixed,aff,ran}_N ≤ γ min{m, m+1-N}/(4m²)` (91). Thus
`𝔇^{fixed,aff,ran}_N = Θ(γ(m+1-N)/m²)` with universal implicit constants. The upper bound uses only raw
queries. For `N ≥ m + 1` the value is zero. The exact randomized decision complexity is `m + 1` for fixed
affine information and `2` for adaptive affine or raw information. The lower bound allows arbitrary real
measurement coefficients and measurable randomized decoders, without a processing-time restriction.

**Formalization Note.** `𝔇^{fixed,aff,ran}_N` is the infimum, over measurable randomized fixed designs
`ExactDesign (NCoord m) Ω N` (arbitrary real rows and offsets, an arbitrary jointly measurable decoder)
on a standard Borel probability seed space, of the worst expected loss on `P_m`; the lower bound is
stated for every such design, the upper bound by a raw design attaining it. Randomized adaptive
algorithms are measurable `AdaptiveAlg` with exact replies run with fuel equal to the budget; the
deterministic two-query algorithm is the one-point-seed case. The universal `Θ` constants are chosen
before `m`, `γ`, `N`. -/
theorem theorem_21 :
    (∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ N : ℕ, N ≤ m →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
          ENNReal.ofReal (γ * ((m : ℝ) + 1 - N) / (192 * Real.pi ^ 2 * (m : ℝ) ^ 2)) ≤
            designRegret (nBox m) (nLoss m γ) μ D) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D ≤
            ENNReal.ofReal (γ * min (m : ℝ) ((m : ℝ) + 1 - N) / (4 * (m : ℝ) ^ 2)))) ∧
      -- the value is zero for `N ≥ m + 1`
      (∀ N : ℕ, m + 1 ≤ N →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ designRegret (nBox m) (nLoss m γ) μ D = 0) ∧
      -- exact randomized fixed affine complexity `m + 1`: no design with at most `m` rows is exact
      (∀ N : ℕ, N ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
        0 < designRegret (nBox m) (nLoss m γ) μ D) ∧
      -- exact randomized adaptive complexity `2`, affine and raw
      (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
        algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A 2 = 0) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω), A.IsExact → A.IsMeasurable →
        0 < algRegret (nBox m) (nLoss m γ) μ A 1)) ∧
    -- the rate `Θ(γ(m+1-N)/m²)` with universal constants
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ N : ℕ, N ≤ m →
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
        ENNReal.ofReal (c * (γ * ((m : ℝ) + 1 - N) / (m : ℝ) ^ 2)) ≤
          designRegret (nBox m) (nLoss m γ) μ D) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
        D.IsMeasurable ∧
        designRegret (nBox m) (nLoss m γ) μ D ≤
          ENNReal.ofReal (C * (γ * ((m : ℝ) + 1 - N) / (m : ℝ) ^ 2)))) := by sorry

end DeepQOperator.Supplement
