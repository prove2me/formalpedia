-- Prove2me | Theorems.Thm_ExponentialJuliaSetMisiurewicz_spherical_sensitive_dependence_exp
-- name    : ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:46.510691+00:00
-- url     : https://prove2.me/theorems/7c5cbdb4-da22-48b2-9404-21d849911d6c
-- title:
--   Exponential Julia Set Misiurewicz: spherical sensitive dependence exp
-- statement:
--   **Corollary 4.4.** The exponential map has sensitive dependence with respect to spherical
--   distance, represented by the ordinary metric on the unit sphere in `ℝ³`.
--
--   Source: https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L187-L200
-- source:
--   https://github.com/LR-UK/exp-chaotic/blob/303b2d3d1121ebc3a86399de8f1e71c17a8b6dd8/ExpChaotic/Spherical.lean#L187-L200

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Spherical
set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section

theorem ExponentialJuliaSetMisiurewicz.spherical_sensitive_dependence_exp :
    HasSensitiveDependenceVia
      (fun w : ℂ => riemannSphereUniformEquivUnitSphere (w : OnePoint ℂ)) := by sorry
