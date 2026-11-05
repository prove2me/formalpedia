-- Prove2me | Theorems.Thm_Exits_tested_append_of_pass
-- name    : Exits.tested_append_of_pass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:43.091011+00:00
-- url     : https://prove2.me/theorems/7ffea189-e416-49a7-8e9d-e9c4dc8b4f16
-- title:
--   Exits: tested append of pass
-- statement:
--   If an entry of the first list passes, nothing of the second list is tested.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L55-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L55-L63

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

theorem Exits.tested_append_of_pass {v : ν → Bool} {A : List ν} (h : A.any v = true) (B : List ν) : tested v (A ++ B) = tested v A := by sorry
