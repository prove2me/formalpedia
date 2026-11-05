-- Prove2me | Theorems.Thm_Eight_ViaGrouping_levelAlgP_gridPsi_keeps
-- name    : Eight.ViaGrouping.levelAlgP_gridPsi_keeps
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:10:50.965822+00:00
-- url     : https://prove2.me/theorems/1f2c4356-87c2-4976-a03b-d38e660e36b0
-- title:
--   Via Grouping: level Alg P grid Psi keeps
-- statement:
--   With the program `gridPsi` for Ψ, the algorithm of one level has polynomial-time steps if the
--   algorithm for networks has.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L58-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L58-L59

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

theorem Eight.ViaGrouping.levelAlgP_gridPsi_keeps (h : StGridPsiPoly) (g : ℕ) {NA : NetAlg} (hN : AlgKeeps NA) : (levelAlgP g (gridPsi g false) (gridPsi g true) NA).Keeps := by sorry
