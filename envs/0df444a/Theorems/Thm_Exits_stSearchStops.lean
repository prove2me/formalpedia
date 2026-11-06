-- Prove2me | Theorems.Thm_Exits_stSearchStops
-- name    : Exits.stSearchStops
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:46:32.825385+00:00
-- url     : https://prove2.me/theorems/918b81b9-c2c8-4cb7-9dab-3690e371afec
-- title:
--   Exits: st Search Stops
-- statement:
--   **Line 10 of Algorithm 1**: «try all groupings into K_ℓ groups until one is good». The search
--   halts at the first good grouping.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/End.lean#L51-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/End.lean#L51-L51

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Exits_Runs
import Definitions.Def_Exits_Poly
import Definitions.Def_Exits_Grouping
import Definitions.Def_Exits_Level
import Definitions.Def_Exits_Count
import Definitions.Def_Exits_Decides
import Definitions.Def_Variance_Grouping
import Definitions.Def_Value_End
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Enumerate_Named
import Definitions.Def_Suffices_Main
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Exits_End
set_option autoImplicit false
section
section
open Exits
open Paper Eight

theorem Exits.stSearchStops : StSearchStops := by sorry
