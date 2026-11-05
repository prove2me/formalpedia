-- Prove2me | Theorems.Thm_CountKSat_Value_ext_val
-- name    : CountKSat.Value.ext_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:20:14.586041+00:00
-- url     : https://prove2.me/theorems/8343f6fc-4da6-420f-a511-f3582606e6f2
-- title:
--   Value: ext val
-- statement:
--   Below n the continued assignment is the assignment.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Value.lean#L30-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Value.lean#L30-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_CountKSat_Value
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open CountKSat
open Finset Groundwork Groundwork.Prog Groundwork.SatNet
open CountKSat.Value

theorem CountKSat.Value.ext_val {n : ℕ} (a : Fin n → Bool) (i : Fin n) : ext a i.val = a i := by sorry
