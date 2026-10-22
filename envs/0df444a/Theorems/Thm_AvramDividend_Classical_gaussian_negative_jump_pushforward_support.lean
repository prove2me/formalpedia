-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_support
-- name    : AvramDividend.Classical.gaussian_negative_jump_pushforward_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:10:43.270979+00:00
-- url     : https://prove2.me/theorems/b47fa384-3fc4-4589-a216-a67eff8689d0
-- title:
--   Negative Lévy jumps push forward to strictly positive magnitudes
-- statement:
--   If a spectrally negative Lévy jump measure assigns zero mass to [0,∞), its pushforward under sign reversal assigns zero mass to (-∞,0]. This follows from the precise half-line preimage under negation and pinned Mathlib Measure.map_apply. It completes the support convention needed to connect the actual mission negative-jump measure with the previously proved positive-magnitude Gaussian Volterra kernel and integrability formulas.
-- source:
--   SpectrallyNegativeLevy.ν_Ici; pinned exact-revision MeasureTheory.Measure.map_apply.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.gaussian_negative_jump_pushforward_support (ν : Measure ℝ)
    (hν : ν (Ici (0 : ℝ)) = 0) :
    (ν.map (fun y : ℝ => -y)) (Iic (0 : ℝ)) = 0 := by sorry
