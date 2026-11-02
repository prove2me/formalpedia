-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_ubv_original_ae_horizon_dominating_stopping_clock_budget_transfer
-- name    : AvramDividend.Classical.avram_wave7_ubv_original_ae_horizon_dominating_stopping_clock_budget_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:18:19.13537+00:00
-- url     : https://prove2.me/theorems/74c01669-3c98-4389-aa1e-314106190b70
-- title:
--   Original UBV full expected Stieltjes budget transfer from one a.s. horizon-dominating source stopping clock
-- statement:
--   For the actual source SpectrallyNegativeLevy P 𝓕 in the unbounded-variation regime and actual admissible D, let S be a genuine 𝓕.rightCont stopping time whose value strictly exceeds the fixed finite real horizon T for P-almost every path. If the complete expected discounted dividendMeasure D Stieltjes budget is bounded by ofReal(w x) over the payment domain clipped at min(ruinTime,S), the identical full ruinTime budget follows. Prove equality of the nested expected Stieltjes integrals using the pathwise finite-horizon payment domain theorem on the given almost-sure event and Mathlib lintegral_congr_ae. The stopped stochastic budget remains an explicit premise. No boundary smoothness or integration decomposition is added.
-- source:
--   Proved exact original pathwise payment-domain equality e0a34e97-9144-43ea-a506-3de6e7680e0c and source filtration IsStoppingTime; corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_ubv_original_ae_horizon_dominating_stopping_clock_budget_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (S : Ω → ℝ≥0∞)
    (hSstop : IsStoppingTime 𝓕.rightCont S)
    (hSbigAE : ∀ᵐ ω ∂P, ENNReal.ofReal T < S ω)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (S ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
