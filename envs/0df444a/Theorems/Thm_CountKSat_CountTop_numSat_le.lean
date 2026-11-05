-- Prove2me | Theorems.Thm_CountKSat_CountTop_numSat_le
-- name    : CountKSat.CountTop.numSat_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:54:38.959064+00:00
-- url     : https://prove2.me/theorems/fa8cb0f0-4f4c-415a-9065-8c4e9f2f1554
-- title:
--   Count Top: num Sat le
-- statement:
--   There are at most 2ⁿ satisfying assignments.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Top/Count.lean#L30-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Top/Count.lean#L30-L32

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

theorem CountKSat.CountTop.numSat_le {n : ℕ} (φ : Sat3.CNF n) : SatK.numSat φ ≤ 2 ^ n := by sorry
