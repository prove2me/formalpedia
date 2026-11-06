-- Prove2me | Theorems.Thm_CircuitLowerBound_TabF_fb_iff
-- name    : CircuitLowerBound.TabF.fb_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:07:00.987742+00:00
-- url     : https://prove2.me/theorems/ee2c49d0-50d1-4f6e-a94e-759cc70704df
-- title:
--   Tab F: fb iff
-- statement:
--   When `pos m` equals `top (nu m)`, the answer is right, given that the variables of the formula
--   of a table have L bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L247-L275
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Cert/TabF.lean#L247-L275

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]

theorem CircuitLowerBound.TabF.fb_iff (hV : StVars) (m : ℕ) (hm : pos m = top (nu m)) :
    fb (List.replicate m ()) = true ↔ Fits (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m) ∧ Sat (tabF (codeOf (nu m)) (2 ^ nu m) (2 ^ nu m)) := by sorry
