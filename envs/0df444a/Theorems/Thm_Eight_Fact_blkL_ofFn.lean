-- Prove2me | Theorems.Thm_Eight_Fact_blkL_ofFn
-- name    : Eight.Fact.blkL_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:08.382302+00:00
-- url     : https://prove2.me/theorems/05045888-899f-4967-806b-b08772e29a85
-- title:
--   Fact: blk L of Fn
-- statement:
--   The blocks of a string as a list are those of the string as a function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L145-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L145-L146

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Eight_MulOut_blkL_ofFn

set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.blkL_ofFn {lam : ℕ} (x : Pieces.Bits lam) (s : ℕ) : blkL (List.ofFn x) s = blockAt x s := by sorry
