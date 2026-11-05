-- Prove2me | Theorems.Thm_Eight_c_net_eq_add
-- name    : Eight.c_net_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:36:56.985202+00:00
-- url     : https://prove2.me/theorems/72e30607-04d6-4b4c-982d-49a419265645
-- title:
--   Eight: c net eq add
-- statement:
--   The Eight construction uses the c net eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L247-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecProof_Network.lean#L247-L252

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
variable {Φ : Formula} {g μ k : ℕ}

theorem Eight.c_net_eq_add {a b : Fin g} (hab : a ≠ b) :
    (net Φ g μ k).c a b = #{t ∈ testsOf Φ g μ k | t.1.1 = a ∧ t.2.1 = b} + #{t ∈ testsOf Φ g μ k | t.1.1 = b ∧ t.2.1 = a} := by sorry
