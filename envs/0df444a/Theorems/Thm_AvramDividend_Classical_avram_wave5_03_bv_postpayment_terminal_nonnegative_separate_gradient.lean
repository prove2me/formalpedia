-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
-- name    : AvramDividend.Classical.avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:40:24.643328+00:00
-- url     : https://prove2.me/theorems/28b04520-30d3-4e2d-9a85-5d54ae7dc1b0
-- title:
--   Actual original-source BV C¹ capped post-payment terminal candidate is nonnegative under separate gradient HJB hypothesis
-- statement:
--   For the original SNLP and actual capped admissible dividend strategy, w of the post-right-payment controlled reserve is nonnegative for every sample and time (including time zero and cap contact) under exactly the BV core's separate C1 interior derivative floor, continuity, nonnegative w(0), zero extension below ruin and positive cap. At nonnegative actual reserve the accepted full-cap BV secant from zero gives w(reserve)≥reserve+w(0)≥0; at negative overshoot the accepted zero extension gives w=0. No global nonnegativity outside the actual terminal states, no C2 regularity, full HJB equality or Itô chain identity is used.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), stopped terminal value sign in the BV inequality. Direct bridge for canonical BV ef7e6c20-a118-46f0-ac94-5b02204bba49; corresponding corrected UBV C2 theorem 567c1077-6ef8-46dd-939d-568ef6ba61fe already Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ w (x + X.X t ω - rightLimit D t ω) := by sorry
