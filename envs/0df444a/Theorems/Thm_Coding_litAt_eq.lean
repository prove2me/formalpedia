-- Prove2me | Theorems.Thm_Coding_litAt_eq
-- name    : Coding.litAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:07:28.368754+00:00
-- url     : https://prove2.me/theorems/aaaf0eed-b61d-4bda-9ce6-0202a45f6ee7
-- title:
--   Coding: lit At eq
-- statement:
--   What stands at place i: the literal of the occurrence (i / 3, i % 3), if this is one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L163-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L163-L169

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
variable {g : ℕ} {Φ : Fml}

theorem Coding.litAt_eq (i : ℕ) : litAt 3 Φ i = if i % 3 < (Φ.getD (i / 3) []).length then some (litOf Φ (i / 3, i % 3)) else none := by sorry
