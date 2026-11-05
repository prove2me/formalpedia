-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_le_Bp
-- name    : Eight.ViaGrouping.Cost.le_Bp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:22.613533+00:00
-- url     : https://prove2.me/theorems/866463bb-ecfa-4d54-a602-da1a19a25627
-- title:
--   Cost: le Bp
-- statement:
--   The exponent P·⌊2g/K⌋ + g²B that the count of the terms and of the g² values in a term gives is
--   at most B'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L68-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L68-L69

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

theorem Eight.ViaGrouping.Cost.le_Bp (K g P B : ℕ) : P * (2 * g / K) + g ^ 2 * B ≤ Bp K g P B := by sorry
