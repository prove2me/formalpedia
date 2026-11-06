-- Prove2me | Theorems.Thm_ExplicitCost_answersOf_readTables
-- name    : ExplicitCost.answersOf_readTables
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:28.818942+00:00
-- url     : https://prove2.me/theorems/895c1e09-420a-4508-b136-773a8e421c37
-- title:
--   Explicit Cost: answers Of read Tables
-- statement:
--   The oracle of the tables read back from an oracle of tables is that oracle.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L89-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallParts.lean#L89-L90

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

theorem ExplicitCost.answersOf_readTables (K lam : ℕ) (W : ℕ → List Bool → ℤ) : answersOf K lam (readTables (answersOf K lam W)) = answersOf K lam W := by sorry
