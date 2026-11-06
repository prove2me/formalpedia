-- Prove2me | Theorems.Thm_ExplicitCost_pw_up
-- name    : ExplicitCost.pw_up
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:11:42.132873+00:00
-- url     : https://prove2.me/theorems/b4ef240c-59cf-4b1c-a809-d084cda8f7ce
-- title:
--   Explicit Cost: pw up
-- statement:
--   A larger exponent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L52-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L52-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.pw_up {X a i j : ℕ} (hX : 2 ≤ X) (ha : a ≤ X ^ i) (h : i ≤ j) : a ≤ X ^ j := by sorry
