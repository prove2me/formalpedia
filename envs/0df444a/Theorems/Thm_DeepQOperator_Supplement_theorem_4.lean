-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_4
-- name    : DeepQOperator.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:42:27.981896+00:00
-- url     : https://prove2.me/theorems/70cb846d-9b4e-4b0a-9994-649902cd28f2
-- title:
--   Theorem 4, p.6 — fixed-accuracy separation for the envelope family
-- statement:
--   Consider the envelope family (13)–(14) on the box $[0,m+1]\times[0,1]^m$, with $m\ge2$ and $0<\gamma<1$. Let $\mathfrak E^{\mathrm{fixed,aff,ran}}_N$ be the infimum, over randomized fixed designs of $N$ arbitrary affine measurements with measurable decoders, of the worst-input expected regret.
--
--   1. Three adaptive raw queries suffice for zero regret on the whole box.
--   2. For every integer $0\le N\le m$,
--   $$
--   \frac{\gamma(m+1-N)}{32\pi^2(\sqrt m+1)^2}\ \le\ \mathfrak E^{\mathrm{fixed,aff,ran}}_N\ \le\ \frac\gamma4\min\Big\{1,\frac{2(m+1-N)}{m}\Big\}, \tag{15}
--   $$
--   and the upper bound is achieved by a fixed randomized raw design.
--   3. For $N\ge m+1$ the value is zero. Thus the fixed randomized exact-decision complexity is $m+1$.
--   4. The fixed regret rate is $\Theta(\gamma(m+1-N)/m)$ for every missing-measurement count, with absolute constants.
--   5. The displayed upper-to-lower ratio is below $461$ for all $m\ge2$.
--
--   The result shows that a fixed decision tolerance needs $m+1$ fixed measurements, while three adaptive raw queries suffice.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: the minimax value is at most $x$ (an upper bound on an infimum) → there is an algorithm of the class whose worst regret is at most $x$; reason: the source proves each upper bound by an explicit algorithm or design it describes
--   - reading: fixed randomized exact-decision complexity is $m+1$ → a design with $m+1$ rows has zero worst regret, and every measurable design with at most $m$ rows has positive worst regret; reason: exact complexity is two-sided: attained at $m+1$ and not at $m$
--   - reading: the rate is $\Theta(\gamma(m+1-N)/m)$ → absolute $c,C>0$, chosen before $m,\gamma,N$, with lower bound $c\gamma(m+1-N)/m$ for every design and a design attaining $C\gamma(m+1-N)/m$, for all $0\le N\le m$; reason: the implied constants are absolute, as in (15)
--   - encoding: the upper-to-lower ratio → the ratio of the two sides of (15) with $\gamma$ cancelled; reason: $\gamma>0$ cancels
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 4 and eq. (15), p.6 (PDF p.9); family (13)–(14), p.6; proof in Appendix B, pp.14–17

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Envelope

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 4 (Fixed-accuracy separation)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive
Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256 9f8f3285…),
Theorem 4, p.6, PDF p.9; proved in Appendix B, pp.14–17).

For the envelope family (13)–(14), `m ≥ 2`, `0 < γ < 1`:
* three adaptive raw queries give zero regret on the whole box `[0, m+1] × [0,1]^m`;
* for every `0 ≤ N ≤ m`,
  `γ(m+1-N)/(32π²(√m+1)²) ≤ 𝔈^{fixed,aff,ran}_N ≤ (γ/4) min{1, 2(m+1-N)/m}` (15), the upper bound
  by a fixed randomized raw design;
* for `N ≥ m + 1` the value is zero, so the fixed randomized exact-decision complexity is `m + 1`;
* the fixed regret rate is `Θ(γ(m+1-N)/m)` for every missing-measurement count;
* the displayed upper-to-lower ratio is below `461` for all `m ≥ 2`.

**Formalization Note.** `𝔈^{fixed,aff,ran}_N` is the infimum over measurable randomized fixed designs
(`ExactDesign`, `N` rows, standard Borel seed) of the worst expected loss on the box; the lower bound is
stated for every design and the upper bound by a design attaining it. The deterministic three-query
algorithm is an `AdaptiveAlg` with seed space `Unit` (Dirac measure), run with fuel `3`. The `Θ` constants
are absolute (chosen before `m`, `γ`, `N`). The ratio is computed with `γ` cancelled. -/
theorem theorem_4 :
    (∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∃ A : AdaptiveAlg (EnvCoord m) Unit, A.IsExact ∧ A.IsRaw (envDictionary m) ∧
        A.IsMeasurable ∧ algRegret (envBox m) (envLoss m γ 0) (Measure.dirac ()) A 3 = 0) ∧
      (∀ N : ℕ, N ≤ m →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (D : ExactDesign (EnvCoord m) Ω N), D.IsMeasurable →
          ENNReal.ofReal
              (γ * ((m : ℝ) + 1 - N) / (32 * Real.pi ^ 2 * (Real.sqrt m + 1) ^ 2)) ≤
            designRegret (envBox m) (envLoss m γ 0) μ D) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (D : ExactDesign (EnvCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (envDictionary m) D ∧
          designRegret (envBox m) (envLoss m γ 0) μ D ≤
            ENNReal.ofReal (γ / 4 * min 1 (2 * ((m : ℝ) + 1 - N) / m)))) ∧
      (∀ N : ℕ, m + 1 ≤ N →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (EnvCoord m) Ω N),
          D.IsMeasurable ∧ designRegret (envBox m) (envLoss m γ 0) μ D = 0) ∧
      (∀ N : ℕ, N ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (EnvCoord m) Ω N), D.IsMeasurable →
        0 < designRegret (envBox m) (envLoss m γ 0) μ D)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 → ∀ N : ℕ, N ≤ m →
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (EnvCoord m) Ω N), D.IsMeasurable →
        ENNReal.ofReal (c * (γ * ((m : ℝ) + 1 - N) / m)) ≤
          designRegret (envBox m) (envLoss m γ 0) μ D) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (EnvCoord m) Ω N),
        D.IsMeasurable ∧
        designRegret (envBox m) (envLoss m γ 0) μ D ≤
          ENNReal.ofReal (C * (γ * ((m : ℝ) + 1 - N) / m)))) ∧
    (∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, N ≤ m →
      (1 / 4 * min 1 (2 * ((m : ℝ) + 1 - N) / m)) /
          (((m : ℝ) + 1 - N) / (32 * Real.pi ^ 2 * (Real.sqrt m + 1) ^ 2)) < 461) := by sorry

end DeepQOperator.Supplement
