-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_image_in_half_plane
-- name    : ExponentialJuliaSetMisiurewicz.image_in_half_plane
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:02:37.226132+00:00
-- url     : https://prove2.me/theorems/b5901ca7-881e-47f5-85c0-208c72144c9d
-- title:
--   Exponential Julia Set Misiurewicz: image in half plane
-- statement:
--   **Each image lies wholly in one open half-plane.** If no forward image of the connected
--   set `V` meets the real axis, then for each `n` the image is entirely in the upper half-plane
--   or entirely in the lower one — by the intermediate value theorem applied to `Im`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L191-L210
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/HalfPlane.lean#L191-L210

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Definitions.Def_ExpChaotic_StripGeometry
import Definitions.Def_ExpChaotic_HalfPlane
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.image_in_half_plane {V : Set ℂ} (hVconn : IsConnected V)
    (hnoreal : ∀ (n : ℕ), ∀ z ∈ V, (expIterate n z).im ≠ 0) (n : ℕ) :
    (∀ z ∈ V, 0 < (expIterate n z).im) ∨ (∀ z ∈ V, (expIterate n z).im < 0) := by sorry
