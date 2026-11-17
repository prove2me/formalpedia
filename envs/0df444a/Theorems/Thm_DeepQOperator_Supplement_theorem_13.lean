-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_13
-- name    : DeepQOperator.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:46:28.843048+00:00
-- url     : https://prove2.me/theorems/80137376-a1c3-4980-9e62-3e82372dd061
-- title:
--   Theorem 13, p.44 — balanced randomized affine regret rate for the normalized family
-- statement:
--   For the normalized family (76)–(78), $m\ge2$, $0<\gamma<1$, every integer $0\le N\le m$ satisfies
--   $$
--   L_{m,N}:=\frac{\gamma(m+1-N)}{16\pi^2m(\sqrt m+1)^2}\ \le\ \mathfrak D^{\mathrm{fixed,aff,ran}}_N\ \le\ \frac{\gamma\min\{m,m+1-N\}}{4m^2}. \tag{80}
--   $$
--   The upper-to-lower ratio is at most $4\pi^2(1+1/\sqrt m)^2<116$ and tends to $4\pi^2$ as $m\to\infty$. Thus the rate is $\Theta(\gamma(m+1-N)/m^2)$ for every missing-measurement count. The upper bound uses raw queries. For $N\ge m+1$ the value is zero. The exact randomized decision complexity is $m+1$ fixed versus $2$ adaptive, for both the affine and the raw oracles.
--
--   The theorem pins the randomized fixed affine regret within a constant factor at every budget.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: the minimax value is at most $x$ (an upper bound on an infimum) → there is an algorithm of the class whose worst regret is at most $x$; reason: the source proves each upper bound by an explicit algorithm or design it describes
--   - reading: for $N\ge m+1$ the value is zero → a measurable fixed raw design with $N$ rows has zero worst regret; reason: reading all $m+1$ coordinates (raw sites) decides exactly
--   - reading: the rate is $\Theta(\gamma(m+1-N)/m^2)$ → absolute $c,C>0$ chosen before $m,\gamma,N$ with a lower bound for every design and an attaining design; reason: the constants of (80) are absolute
--   - reading: exact randomized complexity $m+1$ fixed versus $2$ adaptive, affine and raw → every measurable design with $\le m$ rows has positive worst regret; a deterministic two-query raw algorithm is exact; every measurable randomized one-query affine algorithm has positive worst regret; reason: exact complexity is two-sided; raw queries are affine
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 13 and eq. (80), p.44 (PDF p.47); proof in Appendix K

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Normalized

open MeasureTheory Filter Topology

namespace DeepQOperator.Supplement

/-- **Theorem 13 (Balanced randomized affine regret rate)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 13, p.44, PDF p.47; proved in §L.2 p.45 and Appendix K).

For the normalized family (76)–(78), `m ≥ 2`, `0 < γ < 1`, and every integer `0 ≤ N ≤ m`,
`L_{m,N} := γ(m+1-N)/(16π²m(√m+1)²) ≤ 𝔇^{fixed,aff,ran}_N ≤ γ min{m, m+1-N}/(4m²)` (80). The
upper-to-lower ratio is at most `4π²(1 + 1/√m)² < 116`, and this bound tends to `4π²` as `m → ∞`.
Thus the rate is `Θ(γ(m+1-N)/m²)` for every missing-measurement count. The upper bound uses raw
queries. For `N ≥ m + 1` the value is zero. The exact randomized decision complexity is `m + 1` for
fixed and `2` for adaptive information, for both the affine and the raw oracle.

**Formalization Note.** `𝔇^{fixed,aff,ran}_N` is the infimum, over measurable randomized fixed designs
`ExactDesign (NCoord m) Ω N` on a standard Borel probability seed space, of the worst expected loss
`designRegret` on `P_m`; the lower bound is stated for every such design, the upper bound by a raw
design attaining it. Randomized adaptive algorithms are measurable `AdaptiveAlg` with exact replies run
with fuel equal to the budget; the deterministic two-query algorithm is the one-point-seed case
(`Unit`, Dirac measure). The `Θ` constants are absolute: chosen before `m`, `γ`, `N`. The ratio is
computed with `γ` cancelled. -/
theorem theorem_13 :
    (∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ N : ℕ, N ≤ m →
        (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
          ENNReal.ofReal
              (γ * ((m : ℝ) + 1 - N) / (16 * Real.pi ^ 2 * m * (Real.sqrt m + 1) ^ 2)) ≤
            designRegret (nBox m) (nLoss m γ) μ D) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D ≤
            ENNReal.ofReal (γ * min (m : ℝ) ((m : ℝ) + 1 - N) / (4 * (m : ℝ) ^ 2)))) ∧
      -- the value is zero for `N ≥ m + 1`, already for raw designs
      (∀ N : ℕ, m + 1 ≤ N →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (D : ExactDesign (NCoord m) Ω N),
          D.IsMeasurable ∧ IsRawDesign (nDictionary m) D ∧
          designRegret (nBox m) (nLoss m γ) μ D = 0) ∧
      -- exact randomized fixed complexity `m + 1`: no design with at most `m` rows is exact
      (∀ N : ℕ, N ≤ m → ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (NCoord m) Ω N), D.IsMeasurable →
        0 < designRegret (nBox m) (nLoss m γ) μ D) ∧
      -- exact randomized adaptive complexity `2`, affine and raw
      (∃ A : AdaptiveAlg (NCoord m) Unit, A.IsExact ∧ A.IsRaw (nDictionary m) ∧ A.IsMeasurable ∧
        algRegret (nBox m) (nLoss m γ) (Measure.dirac ()) A 2 = 0) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (NCoord m) Ω), A.IsExact → A.IsMeasurable →
        0 < algRegret (nBox m) (nLoss m γ) μ A 1)) ∧
    -- the upper-to-lower ratio
    (∀ m : ℕ, 2 ≤ m → ∀ N : ℕ, N ≤ m →
      (min (m : ℝ) ((m : ℝ) + 1 - N) / (4 * (m : ℝ) ^ 2)) /
          (((m : ℝ) + 1 - N) / (16 * Real.pi ^ 2 * m * (Real.sqrt m + 1) ^ 2)) ≤
        4 * Real.pi ^ 2 * (1 + 1 / Real.sqrt m) ^ 2) ∧
    (∀ m : ℕ, 2 ≤ m → 4 * Real.pi ^ 2 * (1 + 1 / Real.sqrt m) ^ 2 < 116) ∧
    Tendsto (fun m : ℕ => 4 * Real.pi ^ 2 * (1 + 1 / Real.sqrt m) ^ 2) atTop
      (𝓝 (4 * Real.pi ^ 2)) ∧
    -- the rate `Θ(γ(m+1-N)/m²)` with absolute constants
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
