-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_foldl_stepE
-- name    : ClauseBound.Inst.Half.foldl_stepE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:07.487949+00:00
-- url     : https://prove2.me/theorems/e9b845a6-a034-425b-ba72-654d034c8850
-- title:
--   Half: foldl step E
-- statement:
--   The first j steps of round k + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L199-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L199-L211

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.foldl_stepE (W k j : ℕ) (hj : j ≤ W + 1) :
    (List.range j).foldl (stepE (k + 1) (tabK W k)) [] = (List.range j).map fun E => partsLe E (k + 1) := by sorry
