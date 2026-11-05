-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_Labs_sum_map_flatMap
-- name    : ClauseBound.Inst.Half.Labs.sum_map_flatMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:40:05.307078+00:00
-- url     : https://prove2.me/theorems/c046eb3b-406a-4e6e-ba3e-4e92d9f85f47
-- title:
--   Labs: sum map flat Map
-- statement:
--   The sum of z over w.flatMap e is the sum, over the members a of w, of the sums of z over e a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L67-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/HalfLabs.lean#L67-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_ClauseBound_Inst_HalfLabs
import Theorems.Thm_ClauseBound_Boson_Dual_sum_map_flatMap
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Finset Groundwork PaddedDescent.F ClauseBound.Part Partitions
open Labs
open ClauseBound.Inst.Half.Labs

theorem ClauseBound.Inst.Half.Labs.sum_map_flatMap {α β : Type} (w : List α) (e : α → List β) (z : β → ℤ) :
    ((w.flatMap e).map z).sum = (w.map fun a => ((e a).map z).sum).sum := by sorry
