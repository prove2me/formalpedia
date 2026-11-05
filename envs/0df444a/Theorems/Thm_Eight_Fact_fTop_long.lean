-- Prove2me | Theorems.Thm_Eight_Fact_fTop_long
-- name    : Eight.Fact.fTop_long
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:28.009349+00:00
-- url     : https://prove2.me/theorems/ea9c5033-aa2c-4b34-8fdd-8af270089aea
-- title:
--   Fact: f Top long
-- statement:
--   The first function at θ = (Q, θ'): f(·,θ) = f_Q(·,θ') if |Q| = i, and 0 otherwise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L197-L199
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L197-L199

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Definitions.Def_Eight_SecCrossing_Chunk
import Definitions.Def_Eight_SecCrossing_MulOut
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Fact
import Theorems.Thm_Groundwork_PolyT_count
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.count
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset
open Eight.Fact

theorem Eight.Fact.fTop_long {tr : Bool} {i : ℕ} {a b Q w : List Bool} (hL : useLong tr a.length i = true) (hQ : Q.length = tOf a.length) :
    fTop (tr, i, a, b, Q ++ w) = if Q.count true = i then prodL (tOf a.length) (topAt tr Q w a b) else 0 := by sorry
