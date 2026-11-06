-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stLevelKeepsP
-- name    : Eight.ViaGrouping.stLevelKeepsP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:11:25.845248+00:00
-- url     : https://prove2.me/theorems/c30dad60-b92d-4b96-852c-9dcdf6be65f4
-- title:
--   Via Grouping: st Level Keeps P
-- statement:
--   The algorithm of one level has polynomial-time steps, if NA has (for P in unary) and psiR, psiC
--   are polynomial-time functions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L41-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.stLevelKeepsP : StLevelKeepsP := by sorry
