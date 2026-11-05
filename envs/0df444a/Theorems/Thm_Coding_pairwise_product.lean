-- Prove2me | Theorems.Thm_Coding_pairwise_product
-- name    : Coding.pairwise_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:27:57.738665+00:00
-- url     : https://prove2.me/theorems/91d4e227-4ac8-45fd-9d48-8c99e7441223
-- title:
--   Coding: pairwise product
-- statement:
--   The product of two lists that are increasing for r₁ and r₂ is increasing for the order of the
--   dictionary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L40-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Coding/OccLists.lean#L40-L51

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

theorem Coding.pairwise_product {α β : Type} {r₁ : α → α → Prop} {r₂ : β → β → Prop} {l₁ : List α} {l₂ : List β} (h₁ : l₁.Pairwise r₁) (h₂ : l₂.Pairwise r₂) :
    (l₁ ×ˢ l₂).Pairwise fun p q => r₁ p.1 q.1 ∨ (p.1 = q.1 ∧ r₂ p.2 q.2) := by sorry
