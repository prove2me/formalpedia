-- Prove2me | Theorems.Thm_CountKSat_Value_ext_of_le
-- name    : CountKSat.Value.ext_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:57:57.404011+00:00
-- url     : https://prove2.me/theorems/a9c209db-dcd8-4369-8c6c-b1714c51f33b
-- title:
--   Value: ext of le
-- statement:
--   From n on the continued assignment is false.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Value.lean#L34-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Value.lean#L34-L35

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

theorem CountKSat.Value.ext_of_le {n i : ℕ} (a : Fin n → Bool) (h : n ≤ i) : ext a i = false := by sorry
