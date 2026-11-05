-- Prove2me | Theorems.Thm_Eight_network_exponent_lt
-- name    : Eight.network_exponent_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:39:09.01829+00:00
-- url     : https://prove2.me/theorems/b1a24005-11e6-4fc4-b9d6-5d61b49dcd62
-- title:
--   Eight: network exponent lt
-- statement:
--   **Section 6, «Cost».** «With e = δ'/12, K ≥ 72 and 1/K ≤ δ'/72, the exponent in Lemma 1 is eU +
--   e·gP/K + 2gP/K < ½δ'm + (1/144)δ'(m + g) + (1/6)δ'(m + g) = (97/144)δ'm + (25/144)δ'g», from U < 6m
--   and gP ≤ 6(m + g). Same as in the
--   paper, with the strict inequality. K ≥ 72 follows from K ≥ 72/δ' and δ' ≤ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L390-L394
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L390-L394

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper

theorem Eight.network_exponent_lt {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U < 6 * m) (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K < 97 / 144 * δ' * m + 25 / 144 * δ' * g := by sorry
