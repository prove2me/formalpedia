-- Prove2me | Theorems.Thm_Eight_ViaGrouping_is_mono_B
-- name    : Eight.ViaGrouping.is_mono_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:06:42.646704+00:00
-- url     : https://prove2.me/theorems/a4573170-a514-46a1-ba86-19b438dc0d80
-- title:
--   Via Grouping: is mono B
-- statement:
--   In Definition 2 without (iii), the bound B on the values may be raised.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L49-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L49-L55

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

theorem Eight.ViaGrouping.is_mono_B {g P B B' : ℕ} {N : Net g} (h : N.Is P B) (hB : B ≤ B') : N.Is P B' := by sorry
