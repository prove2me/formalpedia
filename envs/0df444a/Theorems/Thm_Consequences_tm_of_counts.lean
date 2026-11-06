-- Prove2me | Theorems.Thm_Consequences_tm_of_counts
-- name    : Consequences.tm_of_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:40:25.766739+00:00
-- url     : https://prove2.me/theorems/b0915658-d853-4493-9366-5684d272250a
-- title:
--   Consequences: tm of counts
-- statement:
--   From a machine cut into polynomial-time steps that returns f(G, s) within c·2^{(δ/2)n} steps to
--   a Turing machine with finite alphabets that, started on the code of (G, s), s ≤ n, halts with
--   `post (f n G s)` within ⌊C·2^{δn}⌋ steps, for every polynomial-time `post` from numbers to words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Main.lean#L40-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Consequences/Main.lean#L40-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Consequences_Defs
import Definitions.Def_Consequences_Sets
import Definitions.Def_Consequences_Dom
import Definitions.Def_SplitCount_Main
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_Eight_ViaGrouping_CorENP
import Definitions.Def_GraphProblems_Host
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_Consequences_Main
set_option autoImplicit false
section
section
open Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount Turing

theorem Consequences.tm_of_counts {Ms : StepMachine (List Bool) ℕ} (hp : PolyTimeSteps Ms) {f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ} {δ : ℝ} (hδ : 0 < δ) {c : ℕ} (h : CountsGraph Ms f (δ / 2) c)
    (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
      Outputs M (codeWith G s) (post (f n G s)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by sorry
