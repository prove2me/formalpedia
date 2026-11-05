-- Prove2me | Theorems.Thm_Exits_met_nil
-- name    : Exits.met_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:18.325173+00:00
-- url     : https://prove2.me/theorems/f574fdd0-fb55-4786-b71b-84f891436e2f
-- title:
--   Exits: met nil
-- statement:
--   No point is met on the empty orbit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L148-L148
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Tested.lean#L148-L148

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

theorem Exits.met_nil (f : γ → τ → γ) (stop : γ → Bool) (c : γ) : met f stop c [] = [] := by sorry
