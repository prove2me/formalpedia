-- Prove2me | Theorems.Thm_Exits_stThroughEStarOf
-- name    : Exits.stThroughEStarOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:32:03.37034+00:00
-- url     : https://prove2.me/theorems/3c6285d0-2b34-4b7a-8eb5-0f639439840e
-- title:
--   Exits: st Through EStar Of
-- statement:
--   **Theorem 2 in its decision form by the proof of Section 6**, sentence by sentence (the comments
--   quote the paper), from e* = 0, Lemma 4 as an enumeration, and the proof for a named machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L99-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L99-L115

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate

theorem Exits.stThroughEStarOf : StThroughEStarOf := by sorry
