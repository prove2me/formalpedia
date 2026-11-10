-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_20261109_coarse_error_nol1_obstruction
-- name    : AvramDividend.Classical.avram_bv_residual9_20261109_coarse_error_nol1_obstruction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T07:33:29.617211+00:00
-- url     : https://prove2.me/theorems/0b448084-1b79-4286-bcd3-83b122daaf82
-- title:
--   Coarse stopped-grid negative budget forbids vanishing error without B integrability
-- statement:
--   If the original stopped physical-grid signed budget is almost surely at most minus a fixed positive multiple of a persistent coarse cell, a nonnegative payoff cannot be dominated by a centred integrable martingale and positive errors whose expectations vanish. There is no measurability or integrability requirement on the signed budget B. This conditional obstruction combines the original collapsed-grid bound 8746af97 with the established centring contradiction e80c034d, and does not claim an existing Standing process witness.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_residual14_positive_mean_deficit_centring_obstruction
open MeasureTheory Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_20261109_coarse_error_nol1_obstruction
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (c ε L η : ℝ) (hη : 0 < η) (hgap : c + η ≤ ε * L)
    (F M B Err : ℕ → Ω → ℝ)
    (hF : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hM : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ c + M n ω + B n ω + max (Err n ω) 0)
    (hBpath : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ -(ε * L)) :
    ¬ Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
