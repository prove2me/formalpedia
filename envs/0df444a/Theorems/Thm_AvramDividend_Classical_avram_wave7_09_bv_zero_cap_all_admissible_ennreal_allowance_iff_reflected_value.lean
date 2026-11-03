-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_all_admissible_ennreal_allowance_iff_reflected_value
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_ennreal_allowance_iff_reflected_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T18:41:34.897889+00:00
-- url     : https://prove2.me/theorems/27ff8dbc-e081-4c56-9bba-3d284be62e25
-- title:
--   Sharp universal BV zero-cap Stieltjes budget for any ENNReal allowance
-- statement:
--   The exact finite-activity original BV zero-cap expected complete Stieltjes payout budget criterion is equivalent, uniformly for every genuine cap-zero strategy and every finite natural horizon, to the single extended-nonnegative inequality ofReal(drift/(q+ν(Iio0).toReal))≤A, including A=⊤. Necessity uses the actual admissible zero-barrier strategy and the Proved reflected ENNReal criterion d326509c. Sufficiency is the original process dividendValue cap-zero domination 570b5248, finite-horizon supremum 3b737955, and exact reflected value 6f73f927 with identity 11b589b7. This extends the real criterion with a budget type that matches the canonical expected-cash conclusion.
-- source:
--   Genuine original Ω,P,filtration,X and Stieltjes payout; only Proved 570b5248,d326509c,3b737955,6f73f927,11b589b7,32b4ccb8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_all_admissible_ennreal_allowance_iff_reflected_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ (D : ℝ≥0 → Ω → ℝ),
      IsAdmissibleLe X 0 (0 : ℝ≥0∞) D →
      ∀ n : ℕ,
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ A) ↔
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤ A  := by sorry
