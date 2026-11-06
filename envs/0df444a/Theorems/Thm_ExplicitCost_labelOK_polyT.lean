-- Prove2me | Theorems.Thm_ExplicitCost_labelOK_polyT
-- name    : ExplicitCost.labelOK_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:02:31.83139+00:00
-- url     : https://prove2.me/theorems/18384798-9933-4037-88d4-43d77106d841
-- title:
--   Explicit Cost: label OK poly T
-- statement:
--   The test of the straight edges against a label.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L116-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L116-L119

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

theorem ExplicitCost.labelOK_polyT {g lam : α → ℕ} {tr : α → Bool} {q : α → FQ} (hg : Unary g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) :
    PolyT fun x => labelOK (g x) (tr x) (lam x) (q x) := by sorry
