-- Prove2me | Theorems.Thm_ExplicitCost_rectStrings_polyT
-- name    : ExplicitCost.rectStrings_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:10.791871+00:00
-- url     : https://prove2.me/theorems/e58e3e4b-cf42-4cfb-9f33-8ab1097eb0b7
-- title:
--   Explicit Cost: rect Strings poly T
-- statement:
--   The four strings of a rectangle.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L89-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyQueries.lean#L89-L91

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

theorem ExplicitCost.rectStrings_polyT {g lam i i' : α → ℕ} {tr : α → Bool} {q : α → PsiQ} (hg : PolyT g) (ht : PolyT tr) (hl : PolyT lam) (hq : PolyT q) (hi : PolyT i) (hi' : PolyT i') :
    PolyT fun x => rectStrings (g x) (tr x) (lam x) (q x) (i x) (i' x) := by sorry
