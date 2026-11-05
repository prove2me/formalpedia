-- Prove2me | Theorems.Thm_Eight_Fact_tOf_mono
-- name    : Eight.Fact.tOf_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:54:05.542936+00:00
-- url     : https://prove2.me/theorems/e1b68894-40e0-4462-a8f1-3b4565bcc01b
-- title:
--   Fact: t Of mono
-- statement:
--   ⌈λ/3⌉ does not decrease with λ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L168-L170
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L168-L170

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.tOf_mono {a b : ℕ} (h : a ≤ b) : tOf a ≤ tOf b := by sorry
