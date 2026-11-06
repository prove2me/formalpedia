-- Prove2me | Theorems.Thm_ExplicitCost_digit_eq_zero
-- name    : ExplicitCost.digit_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:58:31.8472+00:00
-- url     : https://prove2.me/theorems/2d132c80-71e8-460f-ad13-eb762cf1eed1
-- title:
--   Explicit Cost: digit eq zero
-- statement:
--   The digits of y beyond its length are 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L83-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyLists.lean#L83-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridProcedures
import Definitions.Def_ClauseBound_Alg_CertGridG
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyLists
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.CertGridG
variable {α : Type} [Enc α]

theorem ExplicitCost.digit_eq_zero (n y r : ℕ) (h : (Nat.bits y).length ≤ r) : digit n y r = 0 := by sorry
