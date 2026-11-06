-- Prove2me | Theorems.Thm_Eight_ViaGrouping_COLOR_counts_of
-- name    : Eight.ViaGrouping.COLOR_counts_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:31:27.346116+00:00
-- url     : https://prove2.me/theorems/b8335c84-c99f-4c0c-ba64-738b0074031e
-- title:
--   Via Grouping: COLOR counts of
-- statement:
--   **Counting the proper colorings, with the procedure named.** For every k ≥ 1 and δ > 0 there are
--   a level ℓ and a threshold parameter τ such that the reader `readC k` followed by `En (max k 2) ℓ τ`
--   has polynomial-time steps and returns, on the code of a graph G on
--   n vertices, the number of proper colorings of G with k colors in n·k + 1 bits, within c·2^{δn}
--   steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorGraph.lean#L58-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/CorGraph.lean#L58-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_Graph
import Definitions.Def_Eight_ViaGrouping_CorDefs2
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Color
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Host
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_CorGraph
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Stepped Paper CountKSat GraphProblems Finset Turing
variable {En : ℕ → ℕ → ℕ → StepMachine (List Unit × Fml) (List Bool)}

theorem Eight.ViaGrouping.COLOR_counts_of (h : EngineCounts En) (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, PolyTimeSteps (Stepped.mapIn (readC k) (En (max k 2) ℓ τ)) ∧
    ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      ∃ T : ℕ, (Stepped.mapIn (readC k) (En (max k 2) ℓ τ)).Runs (code G) T (c * (n + 2) ^ c) (SatK.binary (n * k) (numColorings G k)) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by sorry
