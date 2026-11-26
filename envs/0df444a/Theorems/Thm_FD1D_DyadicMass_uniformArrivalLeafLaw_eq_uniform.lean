-- Prove2me | Theorems.Thm_FD1D_DyadicMass_uniformArrivalLeafLaw_eq_uniform
-- name    : FD1D.DyadicMass.uniformArrivalLeafLaw_eq_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:23.763871+00:00
-- url     : https://prove2.me/theorems/d1c102ab-ec00-40fa-9502-e5d07425b715
-- title:
--   Dyadic Mass: uniform Arrival Leaf Law eq uniform
-- statement:
--   A continuous uniform arrival induces the uniform law on depth-`L` leaves.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean#L133-L138
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean#L133-L138

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass

theorem FD1D.DyadicMass.uniformArrivalLeafLaw_eq_uniform (L : ℕ) :
    uniformArrivalLeafLaw L =
      (FiniteLaw.uniform : FiniteLaw (DyadicNode L)) := by sorry
