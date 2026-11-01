-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_complete_localized_control_reward_bound
-- name    : AvramDividend.Classical.avram_wave4_04b_complete_localized_control_reward_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:58:57.40278+00:00
-- url     : https://prove2.me/theorems/7323f947-df53-4110-a294-b6229c26c53d
-- title:
--   Entire closed-horizon Stieltjes reward bounded by chronological jump secants and interior diffuse gradient integral
-- statement:
--   A pathwise finite-horizon controlled correction estimate on the actual spectrally negative Lévy surplus and actual adapted Stieltjes dividend measure. Under an explicit strictly-interior localisation for every pre-dividend reserve time in [0,T], the original HJB gradient bound and original chronological hjump secant bound, every bit of the discounted Stieltjes reward is dominated by the sum of the true source right-payment test-function drops plus an integral of the test-function derivative against the entire atomless remainder. This includes t=0 and the terminal right atom, absolutely continuous dividend variation and singular-continuous variation. It does not assume all dividends are atomic or any density dD/dt. It is a deterministic control-correction estimate, not the Lévy Itô–Meyer stochastic identity, and does not discharge generator/martingale/local-time conditions.
-- source:
--   Direct consequence of canonically Proved complete discounted actual Stieltjes atom/diffuse reward and source-specific chronological hjump aggregate bound, plus almost-everywhere localisation of the diffuse measure and Mathlib lintegral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_complete_stieltjes_atom_diffuse
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_discounted_right_atom_hjump_tsum_bound

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04b_complete_localized_control_reward_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (q : ℝ)
    (hloc : ∀ t : ℝ≥0, t ≤ T →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧ NullSingletonClass μdiffuse ∧
      (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      (∑' s : A,
        ENNReal.ofReal
          (w (riskProcess X x D (s : ℝ).toNNReal ω) -
            w (riskProcess X x D (s : ℝ).toNNReal ω -
              (rightLimit D (s : ℝ).toNNReal ω -
                D (s : ℝ).toNNReal ω))) *
          ENNReal.ofReal (Real.exp (-(q * (s : ℝ))))) +
      (∫⁻ s : ℝ,
        ENNReal.ofReal (Real.exp (-(q * s))) *
          ENNReal.ofReal (deriv w (riskProcess X x D s.toNNReal ω))
            ∂μdiffuse) := by sorry
