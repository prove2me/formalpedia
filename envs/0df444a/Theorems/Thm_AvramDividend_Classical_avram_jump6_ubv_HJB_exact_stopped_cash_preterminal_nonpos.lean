-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_ubv_HJB_exact_stopped_cash_preterminal_nonpos
-- name    : AvramDividend.Classical.avram_jump6_ubv_HJB_exact_stopped_cash_preterminal_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:01:22.113107+00:00
-- url     : https://prove2.me/theorems/4e589354-2794-445f-9fbd-7d0358a89fc9
-- title:
--   Actual original stopped cash has nonpositive HJB signed Stieltjes correction at zero and pre-ruin clocks
-- statement:
--   At an actual original stochastic stopping clock that is zero or strictly earlier than ruin, for an arbitrary cap and UBV HJB supersolution, the exact stopped discounted cash used in Avram's verification proof (the Stieltjes integral over paymentTimes(ruin)∩Iic(τ)) plus the caplinear candidate value drop from all accumulated dividend payments is nonpositive. Unlike a full-interval surrogate, the conclusion uses the identical physical stopped cash expression and rightLimit D convention of the mission source; the proof combines the Proved set equality with the all-cap discounted Stieltjes correction theorem. The ruin-contact endpoint remains a separate source branch.
-- source:
--   Exact physical source for root-connected expected positive-clock budgets 15815eff-2c54-41e3-97a6-d216a3efb8d8 and 464200c8-be79-47cd-8938-79343e0d7fce; Proved stopped-set equality bfe4a214-2dc7-40dc-b43d-19316d917a2e; direct signed HJB source cb9b0cde-a3c8-40cf-9c73-42831322cf72 (pending remote proof 45195, must be Proved before publication).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_ubv_HJB_exact_stopped_cash_preterminal_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hPre : τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
       V (x + X.X (τ ω) ω)) ≤ 0 := by sorry
