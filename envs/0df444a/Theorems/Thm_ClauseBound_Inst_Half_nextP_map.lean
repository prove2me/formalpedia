-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_nextP_map
-- name    : ClauseBound.Inst.Half.nextP_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:17:09.359624+00:00
-- url     : https://prove2.me/theorems/2bd14a70-99e8-40a7-a944-d1a54e4846cc
-- title:
--   Half: next P map
-- statement:
--   The recurrence computes p(N) from p(0), …, p(N − 1), for N ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L103-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfPart.lean#L103-L113

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

theorem ClauseBound.Inst.Half.nextP_map (E : ℕ) : nextP ((List.range (E + 1)).map p) = p (E + 1) := by sorry
