-- Prove2me | Theorems.Thm_Eight_Fact_lenW_eq
-- name    : Eight.Fact.lenW_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:49.975202+00:00
-- url     : https://prove2.me/theorems/ea83732b-cde4-48a1-96f0-c76eba60dd78
-- title:
--   Fact: len W eq
-- statement:
--   For |Q| = i the index θ' has 3(t − i) + 6i = 3t + 3i bits row-wise and 6(t − i) + 3i = 3t + 3(t
--   − i) bits column-wise.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L208-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Fact.lean#L208-L215

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

theorem Eight.Fact.lenW_eq {tr : Bool} {t i : ℕ} {Q : List Bool} (hQ : Q.length = t) (hc : Q.count true = i) :
    lenW tr Q t = 3 * t + 3 * (bif tr then t - i else i) := by sorry
