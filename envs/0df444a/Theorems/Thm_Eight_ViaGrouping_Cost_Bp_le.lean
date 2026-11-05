-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_Bp_le
-- name    : Eight.ViaGrouping.Cost.Bp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:04:47.620841+00:00
-- url     : https://prove2.me/theorems/98383e2d-2d2b-4197-a24d-d39b8dccc285
-- title:
--   Cost: Bp le
-- statement:
--   B' ≤ (2g + g²)(P + B): B' is polynomial in P + B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L72-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L72-L81

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

theorem Eight.ViaGrouping.Cost.Bp_le {K : ℕ} (g P B : ℕ) (hK : 1 ≤ K) : Bp K g P B ≤ (2 * g + g ^ 2) * (P + B) := by sorry
