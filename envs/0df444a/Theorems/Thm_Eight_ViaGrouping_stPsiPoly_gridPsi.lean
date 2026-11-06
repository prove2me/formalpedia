-- Prove2me | Theorems.Thm_Eight_ViaGrouping_stPsiPoly_gridPsi
-- name    : Eight.ViaGrouping.stPsiPoly_gridPsi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:08:38.957026+00:00
-- url     : https://prove2.me/theorems/7128c4cf-4f69-45c9-8921-8d05e2e9daad
-- title:
--   Via Grouping: st Psi Poly grid Psi
-- statement:
--   The program `gridPsi` is polynomial-time in the form that the level asks for.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L47-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L47-L47

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

theorem Eight.ViaGrouping.stPsiPoly_gridPsi (h : StGridPsiPoly) (g : ℕ) (tr : Bool) : StPsiPoly (gridPsi g tr) := by sorry
