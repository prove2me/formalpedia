-- Prove2me | Theorems.Thm_Exits_tested_cons_of_pass
-- name    : Exits.tested_cons_of_pass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:29.9522+00:00
-- url     : https://prove2.me/theorems/9f552105-a3b2-4a0e-b9a9-6015bb611be3
-- title:
--   Exits: tested cons of pass
-- statement:
--   If the first entry passes, it alone is tested: «if … then return».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L35-L35

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

theorem Exits.tested_cons_of_pass {v : ν → Bool} {x : ν} (h : v x = true) (l : List ν) : tested v (x :: l) = [x] := by sorry
