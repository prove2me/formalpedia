-- Prove2me | Theorems.Thm_Eight_Fact_abs_fBot_le
-- name    : Eight.Fact.abs_fBot_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:23.567574+00:00
-- url     : https://prove2.me/theorems/a31c2281-bf9c-418e-8e1d-e9160dc67d75
-- title:
--   Fact: abs f Bot le
-- statement:
--   All values of the second function are at most 2^t in absolute value, t = ⌈λ/3⌉, λ the length of
--   its first string; θ is any list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L183-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L183-L194

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.abs_fBot_le (q : Bool × ℕ × List Bool × List Bool × List Bool) : |fBot q| ≤ 2 ^ tOf q.2.2.1.length := by sorry
