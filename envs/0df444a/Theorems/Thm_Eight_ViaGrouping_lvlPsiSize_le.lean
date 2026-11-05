-- Prove2me | Theorems.Thm_Eight_ViaGrouping_lvlPsiSize_le
-- name    : Eight.ViaGrouping.lvlPsiSize_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:43.731408+00:00
-- url     : https://prove2.me/theorems/28cd1d34-5c1d-4987-87bb-fb84681cd04a
-- title:
--   Via Grouping: lvl Psi Size le
-- statement:
--   The sizes of a query for Ψ and of its answer add up to at most `lvlPsiSize g`·(size of c + B +
--   λ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L95-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L95-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_StepMachines_Prog_GridDefs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_LevelNet
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Stepped Finset Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.lvlPsiSize_le (g sc B n sy B' : ℕ) (hn : 1 ≤ n) (hy : sy ≤ 2 * nRect g * n + 1) (hB' : B' ≤ g * B + g ^ 2 * n) :
    sc + sy + 2 * size g + 4 * (g ^ 3 * n) + B' + 8 ≤ lvlPsiSize g * (sc + B + n) := by sorry
