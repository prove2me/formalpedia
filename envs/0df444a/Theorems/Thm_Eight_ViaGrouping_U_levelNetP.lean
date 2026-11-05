-- Prove2me | Theorems.Thm_Eight_ViaGrouping_U_levelNetP
-- name    : Eight.ViaGrouping.U_levelNetP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:07:48.796874+00:00
-- url     : https://prove2.me/theorems/77a85e58-d76d-450e-9b1e-691f3dd345f1
-- title:
--   Via Grouping: U level Net P
-- statement:
--   The total is the number that the algorithm compares (`useRowP`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L66-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L66-L66

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

theorem Eight.ViaGrouping.U_levelNetP (g : ℕ) (tr : Bool) (lam y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) : (levelNetP g tr lam y Rm).U = totalG eightF g g tr 0 lam y := by sorry
