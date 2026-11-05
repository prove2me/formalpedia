-- Prove2me | Theorems.Thm_CountKSat_CountTop_outW_eq
-- name    : CountKSat.CountTop.outW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:55:18.362918+00:00
-- url     : https://prove2.me/theorems/55432da4-d4f0-4052-b377-40a8d4f2521f
-- title:
--   Count Top: out W eq
-- statement:
--   The output function `outW` of the machine writes the count v as the n + 1 bits `SatK.binary n v`
--   that the statement of #k-SAT asks for.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Top/Count.lean#L43-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Top/Count.lean#L43-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_WidthK_Top_Sat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Sat
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_WidthK_Top_Sat
import Definitions.Def_CountKSat_Top_Count
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSat CountKSat.CountTop
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)

theorem CountKSat.CountTop.outW_eq (n : ℕ) (ψ : Fml) (v : ℕ) : outW ((List.replicate n (), ψ), v) = SatK.binary n v := by sorry
