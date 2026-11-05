-- Prove2me | Theorems.Thm_Exits_COUNT_polyTimeSteps
-- name    : Exits.COUNT_polyTimeSteps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:38:50.053816+00:00
-- url     : https://prove2.me/theorems/dd369e92-a3f6-460f-a7cd-52cb7fa49106
-- title:
--   Exits: COUNT poly Time Steps
-- statement:
--   The steps of Count, at the level ℓ, take polynomial time, if the algorithm for networks keeps
--   polynomial-time steps and Clique(ℓ) has them. (Section 6: «Z is computed in time O(2^{δ'm}) plus a
--   polynomial in n». The bound on the number of steps bounds the time only together with this.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Count.lean#L43-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Count.lean#L43-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Exits_Level
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Count
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping

theorem Exits.COUNT_polyTimeSteps (hKp : StKeeps) (hC : StClique) (ℓ : ℕ) : PolyTimeSteps (COUNT ℓ) := by sorry
