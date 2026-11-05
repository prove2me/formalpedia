-- Prove2me | Theorems.Thm_Eight_ViaGrouping_NETWORKp_keeps
-- name    : Eight.ViaGrouping.NETWORKp_keeps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:25:39.412883+00:00
-- url     : https://prove2.me/theorems/4d6e865c-a080-49b1-8eb7-9b5ad8be011d
-- title:
--   Via Grouping: NETWORKp keeps
-- statement:
--   The steps of NETWORK(ℓ) are polynomial time, whenever those of the procedures of the network are
--   and P is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L82-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L82-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.NETWORKp_keeps (ℓ : ℕ) : AlgKeeps (NETWORKp ℓ) := by sorry
