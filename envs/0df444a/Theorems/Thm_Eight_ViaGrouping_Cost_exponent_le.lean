-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_exponent_le
-- name    : Eight.ViaGrouping.Cost.exponent_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:01:40.423371+00:00
-- url     : https://prove2.me/theorems/2926349d-9e5d-4278-8295-e1be2b48114a
-- title:
--   Cost: exponent le
-- statement:
--   The exponents: e·K²L + 2gP/K ≤ e·K² + (e·U + (e + 2)·gP/K), from «K²L ≤ K² + U + gP/K». The term
--   e·K² is a constant.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L96-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L96-L101

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

theorem Eight.ViaGrouping.Cost.exponent_le {K : ℕ} (g U P : ℕ) {e : ℝ} (hK : 1 ≤ K) (h0 : 0 ≤ e) :
    e * (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) + 2 * ((g : ℝ) * P) / K ≤ e * (K : ℝ) ^ 2 + (e * U + (e + 2) * ((g : ℝ) * P) / K) := by sorry
