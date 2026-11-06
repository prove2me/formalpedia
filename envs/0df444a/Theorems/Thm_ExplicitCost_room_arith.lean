-- Prove2me | Theorems.Thm_ExplicitCost_room_arith
-- name    : ExplicitCost.room_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:15.524678+00:00
-- url     : https://prove2.me/theorems/eb233db1-f088-42f1-8538-2065d2ba9c5e
-- title:
--   Explicit Cost: room arith
-- statement:
--   The arithmetic of the sizes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L55-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L55-L82

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

theorem ExplicitCost.room_arith (c Cn Cg : ℕ) : ∃ C : ℕ, ∀ X g K p l lam B m n A : ℕ, 2 ≤ X → g * g ≤ X → K ≤ g → p ≤ g → l ≤ g → 2 * lam ≤ X → B ≤ X → m ≤ X ^ c → n ≤ m → A ≤ X ^ (c + 4) →
    20 * (Cn * g + (2 * l + 2 * lam + 2 * B + 2 * p + 2 * K + (n * (m + 2) + 1) + (m + 1) + 2 * (n * (2 * lam + 2) + 1) + 9) + (X * (c * g ^ 4) + 2) + (X * (c * g ^ 4) + (A + g * A) + 2) + (A + (l + 9)) ^ Cg +
      (A + g * A) + (K * g + 2) + g + A + (g ^ 4 * lam + g * A) + 4) ≤ X ^ C := by sorry
