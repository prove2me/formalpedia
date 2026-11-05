-- Prove2me | Theorems.Thm_Exits_threeSat_through_eStar
-- name    : Exits.threeSat_through_eStar
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:45:43.348105+00:00
-- url     : https://prove2.me/theorems/4423da1b-598a-4018-8ea8-ef5a811f9aca
-- title:
--   Exits: three Sat through e Star
-- statement:
--   **Theorem 2 in its decision form, by the proof of Section 6**, through e* = 0: for every δ > 0 a
--   deterministic algorithm decides 3-SAT on n variables, with any number of clauses, in time O(2^{δn})
--   (the decision form of Theorem 2, which counts).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/End.lean#L102-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/End.lean#L102-L102

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

theorem Exits.threeSat_through_eStar : Sat3.ThmEveryDelta := by sorry
