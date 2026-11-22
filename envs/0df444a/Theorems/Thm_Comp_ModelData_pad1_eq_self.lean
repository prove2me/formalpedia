-- Prove2me | Theorems.Thm_Comp_ModelData_pad1_eq_self
-- name    : Comp.ModelData.pad1_eq_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:44:23.302705+00:00
-- url     : https://prove2.me/theorems/b0e699a2-aaf9-4af5-99ea-583ef4022b80
-- title:
--   Model Data: pad1 eq self
-- statement:
--   An enabled action denotes itself. `split_ifs` leaves one goal, not two: the `if` condition is
--       `h` itself, so the negative branch closes on the spot.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L408-L412
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L408-L412

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.pad1_eq_self (d : ModelData) {s a1 : ℕ} (h : a1 ∈ d.keys1 s) :
    d.pad1 s a1 = a1 := by sorry
