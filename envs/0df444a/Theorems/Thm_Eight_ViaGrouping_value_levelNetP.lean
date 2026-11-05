-- Prove2me | Theorems.Thm_Eight_ViaGrouping_value_levelNetP
-- name    : Eight.ViaGrouping.value_levelNetP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:06:45.033103+00:00
-- url     : https://prove2.me/theorems/9c11da3a-99ad-46b5-bc5d-5d9266586da9
-- title:
--   Via Grouping: value level Net P
-- statement:
--   «The value is Z_ι», for the network in the printed form.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L62-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L62-L63

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

theorem Eight.ViaGrouping.value_levelNetP {lam : ℕ} (hlam : 1 ≤ lam) (g : ℕ) (tr : Bool) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    (levelNetP g tr lam y Rm).value = Zι (gridR0 g g lam Rm) (Level.patOf g lam y) := by sorry
