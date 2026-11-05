-- Prove2me | Theorems.Thm_Eight_ViaGrouping_two_le_levelK
-- name    : Eight.ViaGrouping.two_le_levelK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:24:34.968834+00:00
-- url     : https://prove2.me/theorems/e91783c7-f532-40b8-8e8e-bbd3c99bbdbf
-- title:
--   Via Grouping: two le level K
-- statement:
--   K_ℓ ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L49-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L49-L49

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

theorem Eight.ViaGrouping.two_le_levelK (ℓ : ℕ) : 2 ≤ levelK ℓ := by sorry
