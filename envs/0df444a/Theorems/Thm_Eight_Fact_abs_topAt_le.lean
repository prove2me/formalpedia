-- Prove2me | Theorems.Thm_Eight_Fact_abs_topAt_le
-- name    : Eight.Fact.abs_topAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:54:28.783001+00:00
-- url     : https://prove2.me/theorems/0d0df298-76af-4fdd-a466-4de8d427abbf
-- title:
--   Fact: abs top At le
-- statement:
--   The factor of a block in the first function is in {−1, 0, 1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L154-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L154-L158

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

theorem Eight.Fact.abs_topAt_le (tr : Bool) (Q w a b : List Bool) (s : ℕ) : |topAt tr Q w a b s| ≤ 1 := by sorry
