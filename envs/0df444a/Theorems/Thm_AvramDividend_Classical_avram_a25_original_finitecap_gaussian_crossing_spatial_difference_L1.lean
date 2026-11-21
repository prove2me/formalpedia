-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_spatial_difference_L1
-- name    : AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_spatial_difference_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T09:53:24.888665+00:00
-- url     : https://prove2.me/theorems/32d61c6f-7003-4a58-882b-9cec41ee72f4
-- title:
--   True finitecap original caplinear Gaussian crossing spatial increment is L1-integrable
-- statement:
--   Prove L1 integrability of the exact caplinear finitecap spatial difference V(Y+R)-w(Y) for a bounded original controlled reserve Y∈[0,b] and an integrable true original stopped Gaussian increment R. Requires only measurability of the physical crossing value and the original HJB value function continuity plus negative-side zero condition. Uses exact globally linear bound from new a25 scalar Gaussian crossing difference theorem. Addresses the finitecap crossing integrability obligation missing from infinite-cap-only sources, without assuming global boundedness of V.
-- source:
--   Original finitecap physical stopped Gaussian crossing L1 spatial correction envelope; stochastic Gaussian increment R remains original, cash budget not assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_spatial_difference_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (Y R : Ω → ℝ) (hY : ∀ᵐ ω ∂P, 0 ≤ Y ω ∧ Y ω ≤ b)
    (hR : Integrable R P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      (if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) P) :
    Integrable (fun ω =>
      (if Y ω + R ω ≤ b then w (Y ω + R ω)
       else w b + (Y ω + R ω - b)) - w (Y ω)) P := by sorry
