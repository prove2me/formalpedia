-- Prove2me | Theorems.Thm_Exits_mem_of_mem_tested
-- name    : Exits.mem_of_mem_tested
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:53:34.937814+00:00
-- url     : https://prove2.me/theorems/76892011-6b33-4a6d-aed3-2e3e5d4630db
-- title:
--   Exits: mem of mem tested
-- statement:
--   What is tested lies in the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L44-L44

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

theorem Exits.mem_of_mem_tested {v : ν → Bool} {l : List ν} {x : ν} (h : x ∈ tested v l) : x ∈ l := by sorry
