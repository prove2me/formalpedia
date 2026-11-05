-- Prove2me | Theorems.Thm_Coding_place_div_mod
-- name    : Coding.place_div_mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:27:43.574204+00:00
-- url     : https://prove2.me/theorems/996f8f90-30e6-4953-9771-72c575a3846c
-- title:
--   Coding: place div mod
-- statement:
--   The place of the pair (i / 3, i % 3) is i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L103-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L103-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Coding_Defs
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Coding_OccLists
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Coding
open Groundwork Groundwork.Prog Groundwork.Prog.Count
variable {g : ℕ} {Φ : Fml}

theorem Coding.place_div_mod (i : ℕ) : place (i / 3, i % 3) = i := by sorry
