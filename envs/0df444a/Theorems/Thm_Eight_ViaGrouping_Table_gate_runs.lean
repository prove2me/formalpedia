-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_gate_runs
-- name    : Eight.ViaGrouping.Table.gate_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:41.487527+00:00
-- url     : https://prove2.me/theorems/02043cb9-7506-4bed-90bc-822858083874
-- title:
--   Table: gate runs
-- statement:
--   Test z ∈ S_a, then run M or return 0. If M takes at most t ≥ τ steps on states of size at most
--   S' ≥ S whenever z is a setting, then the whole takes at most 2t + 1 steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L178-L183
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L178-L183

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
omit [HasSize C]

theorem Eight.ViaGrouping.Table.gate_runs {α : Type} [HasSize α] (h : IsNetworkP Np c N P B τ S) {u : α} {q : α → C × WQ} {M : Stepped α ℤ} {a : Fin g} {z : List Bool} {t S' : ℕ} {v : ℤ}
    (hq : q u = (c, (a.val, z))) (hz : z.length = N.len a) (ht : τ ≤ t) (hS : S ≤ S') (hM : z ∈ N.S a → M.Runs u t S' v) :
    (gated (mapIn q Np.mem) M).Runs u (2 * t + 1) (size u + S' + 4) (if z ∈ N.S a then v else 0) := by sorry
