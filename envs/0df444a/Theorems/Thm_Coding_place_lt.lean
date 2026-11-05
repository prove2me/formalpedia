-- Prove2me | Theorems.Thm_Coding_place_lt
-- name    : Coding.place_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:02:34.885091+00:00
-- url     : https://prove2.me/theorems/a37deef5-368a-4bc4-ba4f-1608980cf53a
-- title:
--   Coding: place lt
-- statement:
--   The place of an occurrence is one of the 3m places of Φ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L191-L196
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L191-L196

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

theorem Coding.place_lt (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : place o < Φ.length * 3 := by sorry
