-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cofinal_real_nNReal_horizon
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cofinal_real_nNReal_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:22:59.197138+00:00
-- url     : https://prove2.me/theorems/c2a88898-25c0-4620-ad0d-4ea3c4d394a9
-- title:
--   Original admissible strict real cash converges cofinally at genuine nonnegative stopped horizon
-- statement:
--   At every true nonnegative observation clock, the original ruin-stopped discounted Stieltjes cash strictly before the horizon is the real supremum of cash along every monotone cofinal sequence of earlier real cutoffs. The original source strategy's right-limit cumulative dividend amount supplies the finite dominating mass automatically. This removes an additional pathwise finiteness assumption and avoids converting the canonical nonnegative clock into an unrelated real horizon.
-- source:
--   Proved 512282cc source strict cash right-limit bound and Proved e1962f77 original real cofinal identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_real_iSup
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cofinal_real_nNReal_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (S : ℝ≥0) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ (S : ℝ))
    (hcover : ∀ s : ℝ, s < (S : ℝ) → ∃ n, s < u n) :
    (⨆ n : ℕ, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω).toReal := by sorry
