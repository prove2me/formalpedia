-- Prove2me | Theorems.Thm_Eight_ViaGrouping_count_cost_pos_of
-- name    : Eight.ViaGrouping.count_cost_pos_of
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T05:20:14.4042+00:00
-- url     : https://prove2.me/theorems/307414e9-9598-497d-8379-3615594da5be
-- title:
--   Via Grouping: count cost pos of
-- statement:
--   The same in the form that the reduction to sparse formulas takes («… and Φ is satisfiable if and
--   only if Z > 0»): the machine returns an integer that is positive exactly if Φ is satisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L170-L177
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Count.lean#L170-L177

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

theorem Eight.ViaGrouping.count_cost_pos_of {g K : ℕ} {δ' : ℝ} {NA : NetAlg} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hg : 0 < g) (hK : 72 / δ' ≤ K)
    (h : Correct NA g K (δ' / 12) (δ' / 12 + 2)) :
    ∃ A : ℕ, ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) →
      ∃ (T : ℕ) (v : ℤ), (NA.app (satProcs g 3)).Runs Φ T (A * size Φ ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) := by sorry
