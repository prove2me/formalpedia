-- Prove2me | Theorems.Thm_ExplicitCost_pointQuery_polyT
-- name    : ExplicitCost.pointQuery_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:08.09325+00:00
-- url     : https://prove2.me/theorems/996c2544-10ac-4705-acf6-40f0a6e43b80
-- title:
--   Explicit Cost: point Query poly T
-- statement:
--   The entry of the caller's tables at a grid point.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L71-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L71-L74

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

theorem ExplicitCost.pointQuery_polyT {g lam i : α → ℕ} {tr : α → Bool} {q : α → WQ} (hg : Unary g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) (hi : PolyT i) :
    PolyT fun x => pointQuery (g x) (tr x) (lam x) (q x) (i x) := by sorry
