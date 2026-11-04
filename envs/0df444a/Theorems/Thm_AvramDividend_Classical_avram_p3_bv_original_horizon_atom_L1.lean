-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_horizon_atom_L1
-- name    : AvramDividend.Classical.avram_p3_bv_original_horizon_atom_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:31:32.602569+00:00
-- url     : https://prove2.me/theorems/30776939-bdd7-4131-a467-b02fa2c753d2
-- title:
--   Original discounted horizon right-payment atom is integrable
-- statement:
--   The precise discounted payment at the terminal time T, including its original dividend-measure right atom and original ruin payment-times convention, is integrable under the original process probability P. This follows from integrability of the full stopped cash and strict-preterminal cash, together with their exact almost-sure decomposition. No extra Lévy compensation hypothesis is assumed.
-- source:
--   Proved original full reward L1 f97e4695, real horizon split ae, and P3 strict cash L1 67a9c5bf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_horizon_atom_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal) P := by sorry
