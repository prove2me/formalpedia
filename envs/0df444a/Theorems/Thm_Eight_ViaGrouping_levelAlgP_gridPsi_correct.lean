-- Prove2me | Theorems.Thm_Eight_ViaGrouping_levelAlgP_gridPsi_correct
-- name    : Eight.ViaGrouping.levelAlgP_gridPsi_correct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:08:33.422879+00:00
-- url     : https://prove2.me/theorems/9fde5958-dbd6-4811-a129-1427ba980464
-- title:
--   Via Grouping: level Alg P grid Psi correct
-- statement:
--   «Cost» of the proof of Proposition 3, with the program `gridPsi` for Ψ: an algorithm for
--   networks on [g], in the printed form, with the exponent of Lemma 1 gives an algorithm for cliques on
--   g² nodes with the exponent (ρ + 2/K)e + 2/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L52-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelEnd.lean#L52-L54

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

theorem Eight.ViaGrouping.levelAlgP_gridPsi_correct (h : StGridPsi) {K g : ℕ} {e : ℝ} {NA : NetAlg} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hN : Correct NA g K e (e + 2)) :
    (levelAlgP g (gridPsi g false) (gridPsi g true) NA).Correct (g * g) ((rho + 2 / K) * e + 2 / K) := by sorry
