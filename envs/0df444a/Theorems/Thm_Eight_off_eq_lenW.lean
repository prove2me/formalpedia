-- Prove2me | Theorems.Thm_Eight_off_eq_lenW
-- name    : Eight.off_eq_lenW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:27:15.244956+00:00
-- url     : https://prove2.me/theorems/8b0968a2-b42a-4032-b2be-09374f15e0f9
-- title:
--   Eight: off eq len W
-- statement:
--   The index of the block number s begins where the indices of the s earlier blocks end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L96-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L96-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.off_eq_lenW (tr : Bool) (Q : List Bool) (s : ℕ) : off tr Q s = lenW tr Q s := by sorry
