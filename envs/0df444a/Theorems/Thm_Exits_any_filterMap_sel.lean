-- Prove2me | Theorems.Thm_Exits_any_filterMap_sel
-- name    : Exits.any_filterMap_sel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:45.002328+00:00
-- url     : https://prove2.me/theorems/2d5a44c7-9e24-480f-9184-be5b9315cb5f
-- title:
--   Exits: any filter Map sel
-- statement:
--   Some entry passes w if and only if some picked entry passes v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L117-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L117-L123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
variable (sel : τ → Option ν) (v : ν → Bool) (w : τ → Bool) (hw : ∀ x, w x = ((sel x).map v).getD false)
include hw

theorem Exits.any_filterMap_sel (xs : List τ) : (xs.filterMap sel).any v = xs.any w := by sorry
