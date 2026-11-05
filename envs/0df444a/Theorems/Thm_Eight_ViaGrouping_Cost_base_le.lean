-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Cost_base_le
-- name    : Eight.ViaGrouping.Cost.base_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:22:51.599202+00:00
-- url     : https://prove2.me/theorems/8ecdeee0-3cbf-4bc7-8084-9e695cf9a0dc
-- title:
--   Cost: base le
-- statement:
--   B' + L ≤ (4g + g²)(P + B), from «L ≤ 2gP»: the factor (B' + L)^C is polynomial in P + B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L104-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Main.lean#L104-L109

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

theorem Eight.ViaGrouping.Cost.base_le {K g : ℕ} (U P B : ℕ) (hK : 1 ≤ K) (hg : 1 ≤ g) (hP : 1 ≤ P) (hU : U ≤ g * P) :
    Bp K g P B + Paper.groupedLength K g U P ≤ (4 * g + g ^ 2) * (P + B) := by sorry
