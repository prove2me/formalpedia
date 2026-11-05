-- Prove2me | Theorems.Thm_Eight_Fact_abs_fTop_le
-- name    : Eight.Fact.abs_fTop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:23.398317+00:00
-- url     : https://prove2.me/theorems/9b4116a9-f143-476f-af8b-e83334712719
-- title:
--   Fact: abs f Top le
-- statement:
--   All values of the first function are in {−1, 0, 1}, for every input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L173-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L173-L179

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

theorem Eight.Fact.abs_fTop_le (q : Bool × ℕ × List Bool × List Bool × List Bool) : |fTop q| ≤ 1 := by sorry
