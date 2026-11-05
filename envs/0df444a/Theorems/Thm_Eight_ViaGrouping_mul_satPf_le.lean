-- Prove2me | Theorems.Thm_Eight_ViaGrouping_mul_satPf_le
-- name    : Eight.ViaGrouping.mul_satPf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:20:06.777879+00:00
-- url     : https://prove2.me/theorems/91190659-b5bc-4a1c-8804-3170730de949
-- title:
--   Via Grouping: mul sat Pf le
-- statement:
--   gP = 2k·g⌈m/g⌉ ≤ 2k(m + g), for P = max{1, 2k·m̄} and k ≥ 1 (for k = 3 the paper's «gP = 6g⌈m/g⌉
--   ≤ 6(m + g)»).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L79-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L79-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_SatPsi
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_Eight_SecProof_Proof
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Count
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper

theorem Eight.ViaGrouping.mul_satPf_le {k : ℕ} (hk : 1 ≤ k) (g : ℕ) (Φ : Fml) : g * satPf g k Φ ≤ 2 * k * (Φ.length + g) := by sorry
