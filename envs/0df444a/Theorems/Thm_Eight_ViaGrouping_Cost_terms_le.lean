-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_terms_le
-- name    : Eight.ViaGrouping.Cost.terms_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:59:25.635365+00:00
-- url     : https://prove2.me/theorems/2a47733c-538c-41dd-a07a-ec840e317b5b
-- title:
--   Cost: terms le
-- statement:
--   «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} = 2^{2gP/K} terms»: the number 2^{P·⌊2g/K⌋}
--   of strings that `tableM` runs through is at most 2^{2gP/K}. K need not divide 2g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L59-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L59-L61

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

theorem Eight.ViaGrouping.Cost.terms_le (K g P : ℕ) : ((2 ^ (P * (2 * g / K)) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * ((g : ℝ) * P) / K) := by sorry
