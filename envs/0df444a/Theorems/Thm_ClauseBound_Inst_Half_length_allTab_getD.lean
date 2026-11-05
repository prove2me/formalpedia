-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_length_allTab_getD
-- name    : ClauseBound.Inst.Half.length_allTab_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:46.808182+00:00
-- url     : https://prove2.me/theorems/f5cb9004-8ad4-4574-8234-0418dbfed980
-- title:
--   Half: length all Tab get D
-- statement:
--   There are p(E) partitions of E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L234-L235
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L234-L235

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_ListP
import Definitions.Def_ClauseBound_Part_Bits
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_PaddedDescent_F_Fuel
import Definitions.Def_ClauseBound_Inst_HalfPart
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions Finset

theorem ClauseBound.Inst.Half.length_allTab_getD {W E : ℕ} (h : E ≤ W) : ((allTab W).getD E []).length = Partitions.p E := by sorry
