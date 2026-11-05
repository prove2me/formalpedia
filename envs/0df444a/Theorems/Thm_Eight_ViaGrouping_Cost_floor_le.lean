-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_floor_le
-- name    : Eight.ViaGrouping.Cost.floor_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:07:16.108633+00:00
-- url     : https://prove2.me/theorems/7635cdc8-d7e3-45c3-b4cf-8c347a9facf5
-- title:
--   Cost: floor le
-- statement:
--   P·⌊2g/K⌋ ≤ 2gP/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L50-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L50-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost

theorem Eight.ViaGrouping.Cost.floor_le (K g P : ℕ) : ((P * (2 * g / K) : ℕ) : ℝ) ≤ 2 * ((g : ℝ) * P) / K := by sorry
