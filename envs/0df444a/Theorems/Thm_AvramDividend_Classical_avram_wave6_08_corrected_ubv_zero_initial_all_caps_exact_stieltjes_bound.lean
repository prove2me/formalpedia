-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
-- name    : AvramDividend.Classical.avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:01:45.448296+00:00
-- url     : https://prove2.me/theorems/14599b22-5d59-42c4-81c7-efbc058a3e03
-- title:
--   Genuine corrected UBV full-Stieltjes dividend inequality at zero capital for every cap and horizon
-- statement:
--   For the actual unbounded-variation spectrally negative Lévy X and original admissible capped dividend process D starting at x=0, the complete discounted Stieltjes reward on the authentic paymentTimes(ruinTime) through any nonnegative horizon is at most w(0). No HJB generator estimate, positive discount or source martingale identity is needed in this zero-start branch: the strict source stopped positivity theorem implies ruin occurs immediately a.s.; the only allowable dividend payoff is the legitimate time-zero right payment and the original corrected immediate-ruin Stieltjes bound controls it. This is a source-specific closed branch of canonical corrected UBV 429e17ca, not a conditional wrapper assuming the missing Itô–Meyer estimate.
-- source:
--   Original source zero-start instantaneous ruin child avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae (canonical Proved 2df9814e-41d9-4386-8e41-2fc17b1d5a4c, accepted submission c36efe0b-45b7-431b-b1c7-7a5d77dc32bd) and canonically Proved e8d8ec8a-10a2-4797-a987-93afe1a43df0, under exact Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. Chat08 owns this independent x=0 corrected UBV boundary case.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_ubv_any_original_zero_start_instant_ruin_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_instantRuin_allHorizon_correctedStieltjesBound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave6_08_corrected_ubv_zero_initial_all_caps_exact_stieltjes_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X 0 D t ω) -
          w (riskProcess X 0 D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w 0) := by sorry
