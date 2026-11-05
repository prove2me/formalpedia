-- Prove2me | Theorems.Thm_Exits_stDecidesOf
-- name    : Exits.stDecidesOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:32:23.205222+00:00
-- url     : https://prove2.me/theorems/53149e8e-e860-44c9-b1e0-b15275d21f87
-- title:
--   Exits: st Decides Of
-- statement:
--   **Theorem 2 in its decision form for step machines, with the machine named.** From Algorithm 1
--   with the constants of its header and Lemma 4 as an enumeration. «We may assume δ ≤ 1»: the machine
--   for min(δ, 1) serves. «Let M = M(δ/3)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L88-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L88-L95

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

theorem Exits.stDecidesOf : StDecidesOf := by sorry
