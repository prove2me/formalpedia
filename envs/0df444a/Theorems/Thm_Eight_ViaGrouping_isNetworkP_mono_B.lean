-- Prove2me | Theorems.Thm_Eight_ViaGrouping_isNetworkP_mono_B
-- name    : Eight.ViaGrouping.isNetworkP_mono_B
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:06:41.039197+00:00
-- url     : https://prove2.me/theorems/cd703f37-8246-438e-b455-d5bebaf122a0
-- title:
--   Via Grouping: is Network P mono B
-- statement:
--   The same for Definition 2 with its procedures.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L58-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/LevelNet.lean#L58-L59

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

theorem Eight.ViaGrouping.isNetworkP_mono_B {C : Type} {g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B B' τ S : ℕ} (h : IsNetworkP Np c N P B τ S) (hB : B ≤ B') : IsNetworkP Np c N P B' τ S := by sorry
