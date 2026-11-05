-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_W804_exact_real_horizon_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_W804_exact_real_horizon_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:47:42.679121+00:00
-- url     : https://prove2.me/theorems/beb7f2ea-daa1-44d4-8db8-366bbcb5bd85
-- title:
--   Exact W8-04 original real-horizon surviving terminal integrable without stochastic budget
-- statement:
--   For the original Standing BV Levy process and admissible strategy, the exact W8-04 discounted strictly surviving postrightpayment terminal at any real nonnegative horizon T is integrable independently of the dividend budget.
-- source:
--   Original W8-04 first-conjunct exact real T, S:=⟨T,hT⟩ and exp(-(q*T)). Prior Proved original source killed-terminal joint measurability and uniform Standing BV finite-clock pathwise envelope imply integrability; no use of claimed HJB supermartingale inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_uniform_pathwise_terminal_all_finite_clocks_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_W804_exact_real_horizon_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    let H : ℝ≥0 := ⟨T, hT⟩
    Integrable (fun ω =>
      if (H : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X H ω - rightLimit D H ω))
      else 0) P := by sorry
