-- Prove2me | Theorems.Thm_Eight_ViaGrouping_tautInNTimeTM_of
-- name    : Eight.ViaGrouping.tautInNTimeTM_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:02.265641+00:00
-- url     : https://prove2.me/theorems/50adda80-dbf3-4d7a-8cd9-63810d9021dd
-- title:
--   Via Grouping: taut In NTime TM of
-- statement:
--   «A deterministic algorithm is in particular a nondeterministic one»: if a machine M with
--   polynomial-time steps decides k-SAT with the exponent δ/2, then the tautologies among the k-DNF
--   formulas on n variables are recognized in nondeterministic time O(2^{δn}).
--   The Turing machine simulates `verifier M`. If ψ is a tautology, the empty witness is accepted in
--   time; if some witness is accepted, the answer of the machine, which is the same on all witnesses, is
--   «tautology».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L66-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L66-L115

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
open Classical

theorem Eight.ViaGrouping.tautInNTimeTM_of (k : ℕ) {δ : ℝ} (hδ : 0 < δ) {M : StepMachine (List Bool) Bool} (hp : PolyTimeSteps M) {c : ℕ} (hM : Decides M k (δ / 2) c) : TautInNTimeTM k δ := by sorry
