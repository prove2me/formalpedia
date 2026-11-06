-- Prove2me | Theorems.Thm_ExplicitCost_ordered_polyT
-- name    : ExplicitCost.ordered_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:16.602579+00:00
-- url     : https://prove2.me/theorems/3acc948b-59fa-4486-8c6b-bd81cb9745f1
-- title:
--   Explicit Cost: ordered poly T
-- statement:
--   The smaller row first.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L80-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L80-L80

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

theorem ExplicitCost.ordered_polyT {q : α → PsiQ} (hq : PolyT q) : PolyT fun x => ordered (q x) := by sorry
