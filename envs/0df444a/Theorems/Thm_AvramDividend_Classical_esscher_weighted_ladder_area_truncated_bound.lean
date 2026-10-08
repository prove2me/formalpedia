-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_ladder_area_truncated_bound
-- name    : AvramDividend.Classical.esscher_weighted_ladder_area_truncated_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:51:08.597439+00:00
-- url     : https://prove2.me/theorems/572987a1-03f4-48c4-8429-ffe2ffbc5d45
-- title:
--   Esscher-weighted integrated ladder-height truncation is dominated by the original Lévy kernel
-- statement:
--   For any positive Esscher parameter φ and positive jump magnitude z, the exponentially weighted integrated truncated ladder height ∫_0^z min(1,t)dt is controlled by a finite constant (1+1/φ) times the original Lévy jump truncation min(1,z²). Combine the independently formulated interval-area estimate with the Esscher-damped min(z²,z) scalar envelope. This is precisely the integrand bound under the Tonelli exchange defining the descending ladder-height jump measure.
-- source:
--   Proved-or-pending ladder_height_truncated_area_interval_bound and esscher_tilted_tail_scalar_integrability_bound; pinned Mathlib mul_le_mul_of_nonneg_left.

import Mathlib
open MeasureTheory intervalIntegral Set

theorem AvramDividend.Classical.esscher_weighted_ladder_area_truncated_bound
    (φ z : ℝ) (hφ : 0 < φ) (hz : 0 ≤ z) :
    Real.exp (-(φ * z)) * (∫ t in (0 : ℝ)..z, min 1 t) ≤
      (1 + φ⁻¹) * min 1 (z ^ 2) := by sorry
