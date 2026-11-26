-- Prove2me | Theorems.Thm_FD1D_DyadicMass_uniformArrival_mem_dyadicCell
-- name    : FD1D.DyadicMass.uniformArrival_mem_dyadicCell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:17.339403+00:00
-- url     : https://prove2.me/theorems/36b0037b-8c65-421a-830f-9c77d4406a1c
-- title:
--   Dyadic Mass: uniform Arrival mem dyadic Cell
-- statement:
--   Every arrival in `[0,1]` lies in the closed cell carrying its label.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean#L141-L148
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/UniformArrival.lean#L141-L148

import Definitions.Def_FD1D_Spatial
import Definitions.Def_FD1D_UniformArrival
set_option autoImplicit true
open FD1D
noncomputable section
open Set MeasureTheory
open FD1D.DyadicMass

theorem FD1D.DyadicMass.uniformArrival_mem_dyadicCell
    (L : ℕ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    u ∈ dyadicCell (uniformArrivalLeaf L u) := by sorry
