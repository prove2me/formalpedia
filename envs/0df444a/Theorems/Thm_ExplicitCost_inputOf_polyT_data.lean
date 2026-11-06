-- Prove2me | Theorems.Thm_ExplicitCost_inputOf_polyT_data
-- name    : ExplicitCost.inputOf_polyT_data
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:52.234898+00:00
-- url     : https://prove2.me/theorems/8f956017-fa98-4aaa-9edc-ca5c0f97ff96
-- title:
--   Explicit Cost: input Of poly T data
-- statement:
--   What an algorithm for networks is given (`Printed.inputOf`: P, B and the numbers P_a, c_{a,b},
--   in unary) is written down in polynomial time from numbers given in unary, the number g of nodes
--   among them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L162-L169
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L162-L169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyLists
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyQueries
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG Eight Eight.SecNetworks QueryMachines Printed
variable {α : Type} [Enc α]

theorem ExplicitCost.inputOf_polyT_data {g P B : α → ℕ} {len : α → ℕ → ℕ} {cap : α → ℕ → ℕ → ℕ} (hg : Unary g) (hP : Unary P) (hB : Unary B) (hl : Unary fun p : α × ℕ => len p.1 p.2)
    (hc : Unary fun p : α × ℕ × ℕ => cap p.1 p.2.1 p.2.2) : PolyT fun c => inputOf (g c) (P c) (B c) (len c) (cap c) := by sorry
