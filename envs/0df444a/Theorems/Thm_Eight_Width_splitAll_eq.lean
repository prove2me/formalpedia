-- Prove2me | Theorems.Thm_Eight_Width_splitAll_eq
-- name    : Eight.Width.splitAll_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:03:41.74029+00:00
-- url     : https://prove2.me/theorems/239a6685-4cb0-461f-92b1-5b8470ab22e7
-- title:
--   Width: split All eq
-- statement:
--   The Width construction uses the split All eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L66-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Cor/WidthProg.lean#L66-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Width
import Definitions.Def_CountKSat_InOut
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_WidthProg
set_option autoImplicit false
section
section
open Eight Eight.Width
open Groundwork Groundwork.Prog CountKSat

theorem Eight.Width.splitAll_eq : ∀ (x : Fml) (ys : List ℕ), splitAll ys x = allP ys x
  := by sorry
