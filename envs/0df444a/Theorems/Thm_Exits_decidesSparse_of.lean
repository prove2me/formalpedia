-- Prove2me | Theorems.Thm_Exits_decidesSparse_of
-- name    : Exits.decidesSparse_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:29:47.918197+00:00
-- url     : https://prove2.me/theorems/8ea7cb5f-f669-4488-bbff-10cc5abae49a
-- title:
--   Exits: decides Sparse of
-- statement:
--   A machine that decides every 3-CNF with m clauses within A·2^{δ'm} steps does what the reduction
--   of the proof of Theorem 2, read for deciding, asks (to decide whether a 3-CNF Φ with m ≤ Mn clauses
--   is satisfiable, in time O(2^{δ'm}) plus a polynomial in n): the sentence asks for less.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L47-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Exits/Decides.lean#L47-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate

theorem Exits.decidesSparse_of {δ' : ℝ} {M : ℕ} {Mc : StepMachine Formula ℤ} {A : ℕ}
    (h : ∀ Φ : Formula, (∀ C ∈ Φ, C.length ≤ 3) → ∃ (T : ℕ) (v : ℤ), Mc.Runs Φ T (A * size Φ ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length)) :
    DecidesSparse δ' M Mc A := by sorry
