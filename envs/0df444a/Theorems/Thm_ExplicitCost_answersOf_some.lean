-- Prove2me | Theorems.Thm_ExplicitCost_answersOf_some
-- name    : ExplicitCost.answersOf_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:33.996662+00:00
-- url     : https://prove2.me/theorems/e50f8dd9-fd23-4a9a-a26a-9076956ecd57
-- title:
--   Explicit Cost: answers Of some
-- statement:
--   An answer of the oracle: the query names a node and a setting, and the answer is the entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L93-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L93-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallParts
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.answersOf_some {K lam : ℕ} {W : ℕ → List Bool → ℤ} {q : TableQuery} {v : Ans} (h : answersOf K lam W q = some v) : q.1 < K ∧ q.2 ∈ words ((K - 1) * lam) ∧ v = .inl (W q.1 q.2) := by sorry
