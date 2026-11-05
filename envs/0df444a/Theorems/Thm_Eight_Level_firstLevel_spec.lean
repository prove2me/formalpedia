-- Prove2me | Theorems.Thm_Eight_Level_firstLevel_spec
-- name    : Eight.Level.firstLevel_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:00:47.45903+00:00
-- url     : https://prove2.me/theorems/62a7ce34-d09e-4a25-b534-3e605a85d636
-- title:
--   Level: first Level spec
-- statement:
--   The first level is such a level.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/SecPseudocode.lean#L43-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/Level/SecPseudocode.lean#L43-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_Level_SecPseudocode
set_option autoImplicit false
section
section
open Eight Eight.Level
open Groundwork Groundwork.Prog Paper

theorem Eight.Level.firstLevel_spec {δ' : ℝ} (hδ' : 0 < δ') : 72 / δ' ≤ levelK (firstLevel hδ') ∧ Eight.Level.levelE (firstLevel hδ') ≤ δ' / 12 := by sorry
