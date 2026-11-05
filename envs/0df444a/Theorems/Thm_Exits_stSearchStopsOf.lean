-- Prove2me | Theorems.Thm_Exits_stSearchStopsOf
-- name    : Exits.stSearchStopsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:31:09.385778+00:00
-- url     : https://prove2.me/theorems/c632c39b-dda9-4e16-b9a9-576bdbf023c9
-- title:
--   Exits: st Search Stops Of
-- statement:
--   **Line 10 of Algorithm 1**: «try all groupings into K_ℓ groups until one is good». If x is the
--   first number below K^g to which the test says yes, the search halts within 2·(x + 1) steps and
--   returns x. From the same sentence for any loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L44-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Grouping.lean#L44-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_ToTuring_Poly_Range
import Mathlib.Tactic.GCongr
import Definitions.Def_Exits_Grouping
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Stepped Finset Paper Eight Eight.SecNetworks Eight.ViaGrouping Eight.ViaGrouping.Cost

theorem Exits.stSearchStopsOf : StSearchStopsOf := by sorry
