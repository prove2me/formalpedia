-- Prove2me | Theorems.Thm_Eight_card_tests_le
-- name    : Eight.card_tests_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:37:26.539216+00:00
-- url     : https://prove2.me/theorems/aad65156-6989-41bb-877b-15eeb019b2d0
-- title:
--   Eight: card tests le
-- statement:
--   **Section 6.** «… hence at most 3m − 1», for m ≥ 1. Same as in the paper (also if some clauses
--   are empty).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L304-L313
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L304-L313

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper

theorem Eight.card_tests_le {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : #(tests g Φ) ≤ 3 * Φ.length - 1 := by sorry
