-- Prove2me | Theorems.Thm_Eight_length_mulStep
-- name    : Eight.length_mulStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:55.332212+00:00
-- url     : https://prove2.me/theorems/ee21c41f-c31d-40d4-b3c4-80c9169adc92
-- title:
--   Eight: length mul Step
-- statement:
--   One multiplication makes the list longer by one entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L59-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Eight_SecCrossing_MulOut
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial

theorem Eight.length_mulStep (r c : ℤ) (l : List ℤ) : (mulStep r c l).length = l.length + 1 := by sorry
