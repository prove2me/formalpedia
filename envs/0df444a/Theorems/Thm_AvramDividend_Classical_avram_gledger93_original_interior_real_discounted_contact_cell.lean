-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger93_original_interior_real_discounted_contact_cell
-- name    : AvramDividend.Classical.avram_gledger93_original_interior_real_discounted_contact_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:20:59.219563+00:00
-- url     : https://prove2.me/theorems/c0dda24f-049d-4c54-83c4-2c89a170a417
-- title:
--   A finite original interior cash cell absorbs its signed postpayment contact up to discount error
-- statement:
--   Convert the Proved original strictly interior ENNReal cash-cell inequality into the signed real cash-plus-postpayment-contact inequality required by gledger81. Finiteness of the cell dividend measure makes this conversion legal. The original source and dividend strategy remain on the same sample space.
-- source:
--   Strict real-valued original interior cash-cell conversion needed to use Proved gledger83 in Open gledger81 16e988d7. Explicit finite-measure assumption prevents invalid ENNReal infinity subtraction.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
import Theorems.Thm_AvramDividend_Classical_avram_gledger45_global_topcap_monotone_zero_negative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger93_original_interior_real_discounted_contact_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (a b : ℝ≥0) (hab : a ≤ b) (hb : b < ρ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hfinite : dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≠ ⊤) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (b : ℝ))) *
          (w (x + X.X b ω - rightLimit D b ω) -
            w (x + X.X b ω - rightLimit D a ω)) ≤
      q * ((b : ℝ) - (a : ℝ)) *
        (dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))).toReal := by sorry
