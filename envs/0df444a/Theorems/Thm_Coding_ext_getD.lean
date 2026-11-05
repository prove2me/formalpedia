-- Prove2me | Theorems.Thm_Coding_ext_getD
-- name    : Coding.ext_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:10.076207+00:00
-- url     : https://prove2.me/theorems/609e72ac-c385-4a8c-b56c-6577e0ca4828
-- title:
--   Coding: ext get D
-- statement:
--   Two bit strings of the same length with the same bits are equal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L84-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L84-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count

theorem Coding.ext_getD {l l' : List Bool} (hl : l.length = l'.length) (h : ∀ i < l.length, l.getD i false = l'.getD i false) : l = l' := by sorry
