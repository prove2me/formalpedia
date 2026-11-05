-- Prove2me | Theorems.Thm_Coding_mem_tests_iff
-- name    : Coding.mem_tests_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:54:49.647611+00:00
-- url     : https://prove2.me/theorems/d2dcd9c4-ccf8-4ec1-9a00-a64862ecb3a8
-- title:
--   Coding: mem tests iff
-- statement:
--   «the pairs {o₁,o₂}, {o₂,o₃}, … of consecutive occurrences are the equality tests» (Section 6):
--   (o, o') is a test exactly if Lean's network has a link from the place of o to the place of o'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L207-L221
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L207-L221

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

theorem Coding.mem_tests_iff (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o o' : ℕ × ℕ} : (o, o') ∈ tests Φ ↔ o ∈ occAll Φ ∧ o' ∈ occAll Φ ∧ linkB 3 Φ (place o) (place o') = true := by sorry
