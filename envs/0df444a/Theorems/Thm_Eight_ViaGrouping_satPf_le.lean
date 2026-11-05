-- Prove2me | Theorems.Thm_Eight_ViaGrouping_satPf_le
-- name    : Eight.ViaGrouping.satPf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:19:24.515252+00:00
-- url     : https://prove2.me/theorems/caaa5906-0458-4d9f-a5c6-939f4aa1bd0d
-- title:
--   Via Grouping: sat Pf le
-- statement:
--   The Via Grouping construction uses the sat Pf le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L88-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L88-L91

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Paper

theorem Eight.ViaGrouping.satPf_le (g k : ℕ) (Φ : Fml) : satPf g k Φ ≤ 2 * (mu g Φ * k) + 1 := by sorry
