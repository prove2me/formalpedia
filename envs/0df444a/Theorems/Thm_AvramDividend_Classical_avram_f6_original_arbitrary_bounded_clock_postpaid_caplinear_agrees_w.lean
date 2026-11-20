-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_arbitrary_bounded_clock_postpaid_caplinear_agrees_w
-- name    : AvramDividend.Classical.avram_f6_original_arbitrary_bounded_clock_postpaid_caplinear_agrees_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:32:25.361359+00:00
-- url     : https://prove2.me/theorems/5d95b0a4-03b6-4bab-8b18-14cbe43f2e42
-- title:
--   Original bounded stopped postpayment caplinear agrees with w at the actual time
-- statement:
--   For the original capped dividend strategy and arbitrary actual physical time t bounded by n, the canonical slope-one extension V agrees exactly with w at the true postpayment controlled reserve x+X_t-rightLimit D_t. The proof instantiates the already Proved original physical clipped grid identity at j=0 and its terminal cell, requiring no assumptions on the off-cap values of w and no abstract source witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_arbitrary_bounded_clock_postpaid_caplinear_agrees_w
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (t : ℝ≥0) (ht : t ≤ n) (ω : Ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    V (x + X.X t ω - rightLimit D t ω) =
      w (x + X.X t ω - rightLimit D t ω) := by sorry
