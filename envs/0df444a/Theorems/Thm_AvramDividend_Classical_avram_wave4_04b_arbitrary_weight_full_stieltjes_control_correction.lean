-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction
-- name    : AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:37:55.293176+00:00
-- url     : https://prove2.me/theorems/8868562f-47d1-4392-a891-4b97e0b626b2
-- title:
--   Complete actual finite-horizon Stieltjes control correction for stopped payoff weights and support-local hjump/gradient
-- statement:
--   For the actual spectrally negative Lévy source, actual adapted dividend strategy, arbitrary path ω, finite closed horizon and nonnegative payoff weight f, the entire weighted Stieltjes dividend reward is dominated by the true chronological right-payment test-function secant sum plus the complete derivative-weighted atomless dividend integral. The source hjump and strictly interior HJB gradient/localisation assumptions are needed only where f is nonzero in [0,T], so f can be the exact stopped paymentTimes indicator times the discount. Time zero, terminal atoms, absolutely continuous and singular-continuous dividend variation are all retained, without a dt density or atom-only assertion. This is a deterministic full Stieltjes control-correction theorem, not the full Lévy Ito–Meyer stochastic identity.
-- source:
--   Canonical arbitrary-weight source Stieltjes atomic/diffuse measure decomposition and source-weighted chronological hjump sum; finite support of the atomless measure and Mathlib lintegral_mono_ae for the support-local gradient. Does not assume stochastic Ito–Meyer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_finite_horizon_arbitrary_weight_stieltjes_split
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_arbitrary_weight_right_atom_hjump_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_arbitrary_weight_full_stieltjes_control_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞)
    (hloc : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T → f (t : ℝ) ≠ 0 →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s : ℝ, f s ∂μ) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω))) * f (s : ℝ)) +
      (∫⁻ s : ℝ,
        f s * ENNReal.ofReal
          (deriv w (riskProcess X x D s.toNNReal ω)) ∂μdiffuse) := by sorry
