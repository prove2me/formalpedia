-- Prove2me | Theorems.Thm_Exits_filterMap_tested
-- name    : Exits.filterMap_tested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:45:06.56225+00:00
-- url     : https://prove2.me/theorems/0441f8f0-b800-4ddd-b8ce-e7da170b2177
-- title:
--   Exits: filter Map tested
-- statement:
--   The picked entries among those tested by w are the picked entries tested by v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L126-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L126-L141

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

theorem Exits.filterMap_tested (xs : List τ) : (tested w xs).filterMap sel = tested v (xs.filterMap sel) := by sorry
