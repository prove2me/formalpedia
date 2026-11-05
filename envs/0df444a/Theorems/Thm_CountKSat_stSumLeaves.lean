-- Prove2me | Theorems.Thm_CountKSat_stSumLeaves
-- name    : CountKSat.stSumLeaves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:44:10.184818+00:00
-- url     : https://prove2.me/theorems/a8325dae-c6a4-4642-9f6c-0680e46a0421
-- title:
--   Count KSat: st Sum Leaves
-- statement:
--   The lemma on trees, as the interface states it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L120-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CountKSat/Walk.lean#L120-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountKSat_Interfaces
import Definitions.Def_ToTuring_Poly_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Definitions.Def_StepMachines_Prog_Walk
import Mathlib.Tactic.Ring
import Definitions.Def_CountKSat_Walk
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
open CountKSat
open Groundwork Groundwork.Stepped Groundwork.Sparsify
variable {α ν : Type}
open Walk

theorem CountKSat.stSumLeaves : StSumLeaves := by sorry
