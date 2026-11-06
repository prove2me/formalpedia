-- Prove2me | Theorems.Thm_Eight_ViaGrouping_verifier_recognizes
-- name    : Eight.ViaGrouping.verifier_recognizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:35:10.725582+00:00
-- url     : https://prove2.me/theorems/81128b7e-3f1c-40ed-9366-4780d10f14a8
-- title:
--   Via Grouping: verifier recognizes
-- statement:
--   **The verifier.** If M decides k-SAT with the exponent δ and the constant c, then `verifier M`,
--   on every witness w and the code of a k-DNF ψ on n variables, ends within c·2^{δn} steps with the bit
--   «ψ is a tautology».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L49-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorNSETH.lean#L49-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_NSETH
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Host
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorNSETH
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Turing

theorem Eight.ViaGrouping.verifier_recognizes {M : StepMachine (List Bool) Bool} {k : ℕ} {δ : ℝ} {c : ℕ} (h : Decides M k δ c) (n : ℕ) (ψ : DNF n) (hψ : IsKDNF k ψ) (w : List Bool) :
    ∃ (T : ℕ) (b : Bool), (verifier M).Runs (withWitness w (SatK.enc k ψ)) T (c * ((SatK.enc k ψ).length + 1) ^ c) [b] ∧ (b = true ↔ Tautology ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by sorry
