-- Prove2me | Theorems.Thm_ExplicitCost_cLam_unary
-- name    : ExplicitCost.cLam_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:34.513615+00:00
-- url     : https://prove2.me/theorems/bc7bb53b-5536-4b7b-9b85-c434c3868314
-- title:
--   Explicit Cost: c Lam unary
-- statement:
--   The label length of a context is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L66-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L66-L66

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

theorem ExplicitCost.cLam_unary {c : α → Ctx} (hc : PolyT c) : Unary fun x => cLam (c x) := by sorry
