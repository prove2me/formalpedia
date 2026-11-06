-- Prove2me | Theorems.Thm_Eight_ViaGrouping_not_NSETH_TM_of
-- name    : Eight.ViaGrouping.not_NSETH_TM_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:44:27.036195+00:00
-- url     : https://prove2.me/theorems/20de1203-ab2e-4af7-aef0-95e32c8e53fb
-- title:
--   Via Grouping: not NSETH TM of
-- statement:
--   **NSETH is false** (the sentence after Corollary 5), for Turing machines and nondeterministic
--   time in verifier form (`NSETH_TM` of proof/networks/Eight/Cor/NSETHDefs.lean), if for every k ≥ 1
--   and δ > 0 some machine with polynomial-time steps decides k-SAT with the exponent δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L120-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L120-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETH
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorNSETH
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Turing

theorem Eight.ViaGrouping.not_NSETH_TM_of (hS : ∀ k : ℕ, 1 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ M : StepMachine (List Bool) Bool, PolyTimeSteps M ∧ ∃ c : ℕ, Decides M k δ c) : ¬ NSETH_TM := by sorry
