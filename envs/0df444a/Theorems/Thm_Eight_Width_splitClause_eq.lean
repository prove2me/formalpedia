-- Prove2me | Theorems.Thm_Eight_Width_splitClause_eq
-- name    : Eight.Width.splitClause_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:01:43.504043+00:00
-- url     : https://prove2.me/theorems/286c1b56-3e03-42eb-8990-07c0a16af5b0
-- title:
--   Width: split Clause eq
-- statement:
--   The Width construction uses the split Clause eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L56-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L56-L64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_WidthProg
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.Width
open Groundwork Groundwork.Prog CountKSat

theorem Eight.Width.splitClause_eq : ∀ (ys : List ℕ) (C : List (ℕ × Bool)), ys.length ≤ C.length - 3 → splitClause ys C = clauseP ys C
  := by sorry
