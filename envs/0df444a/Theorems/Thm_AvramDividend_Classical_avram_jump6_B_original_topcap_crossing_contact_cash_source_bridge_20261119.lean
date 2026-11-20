-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
-- name    : AvramDividend.Classical.avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:33:05.892885+00:00
-- url     : https://prove2.me/theorems/cb0ccb4c-ef57-404e-8dba-8237f0cf59d5
-- title:
--   True top-cap ruin crossing cell source bound without auxiliary finiteness or payout inequality premises
-- statement:
--   At a strictly earlier canonical grid point and subsequent ruin contact, the true original terminal potential change plus strict intervening cash is bounded by the shrinking pre-contact cash tail. The original dividend monotonicity and authentic inclusive cash-finiteness lemmas discharge all premises of the already Proved crossing-cell bound, preserving the actual stopping clock, discounted Ioo cash and top-cap condition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_original_topcap_crossing_contact_cash_source_bridge_20261119
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hDstrat : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (ρ δ a : ℝ≥0)
    (hleft : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ))
    (hbefore : a < ρ)
    (w : ℝ → ℝ) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
       (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
         Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by sorry
