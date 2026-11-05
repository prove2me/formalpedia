-- Prove2me | Theorems.Thm_Exits_tested_append_of_fail
-- name    : Exits.tested_append_of_fail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:50.443961+00:00
-- url     : https://prove2.me/theorems/528e01f7-5759-49b0-a007-bc2a0a0ac794
-- title:
--   Exits: tested append of fail
-- statement:
--   If no entry of the first list passes, all of it is tested and the search goes on in the second
--   list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L67-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L67-L72

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

theorem Exits.tested_append_of_fail {v : ν → Bool} {A : List ν} (h : A.any v = false) (B : List ν) : tested v (A ++ B) = A ++ tested v B := by sorry
