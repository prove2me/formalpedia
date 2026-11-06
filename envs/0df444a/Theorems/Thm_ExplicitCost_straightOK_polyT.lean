-- Prove2me | Theorems.Thm_ExplicitCost_straightOK_polyT
-- name    : ExplicitCost.straightOK_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:03:13.317612+00:00
-- url     : https://prove2.me/theorems/2813b1b3-ddc4-4204-aca9-ee9208fd32bb
-- title:
--   Explicit Cost: straight OK poly T
-- statement:
--   The test of the straight edges between two rows.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L83-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L83-L86

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

theorem ExplicitCost.straightOK_polyT {g lam : α → ℕ} {tr : α → Bool} {q : α → PsiQ} (hg : Unary g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) :
    PolyT fun x => straightOK (g x) (tr x) (lam x) (q x) := by sorry
