-- Prove2me | Theorems.Thm_Eight_ViaGrouping_algPseudocode_of
-- name    : Eight.ViaGrouping.algPseudocode_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T05:22:59.113051+00:00
-- url     : https://prove2.me/theorems/23b68dab-434b-479c-bde4-e304d71298ec
-- title:
--   Via Grouping: alg Pseudocode of
-- statement:
--   **The deciding form of procedure #Sat of Algorithm 1, from any sparsification.** Let δ > 0, and
--   let the constant M ≥ 1 and the construction S have the property that it suffices to decide whether a
--   3-CNF Φ with m clauses is satisfiable, in time O(2^{δ'm}) (`Eight.SufficesSparse δ M S`). Let
--   δ' = min(δ/(3M), 1). At every level ℓ with K_ℓ ≥ 72/δ' and e_ℓ ≤ δ'/12, the machine S(COUNT) decides
--   3-SAT within c·2^{δn} steps. Lemma 4 is used only through that property. Only steps are counted
--   here. That they take polynomial time: `COUNTp_polyTimeSteps` and the first part of
--   `Eight.SufficesSparse`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L104-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Alg.lean#L104-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level

theorem Eight.ViaGrouping.algPseudocode_of {δ M : ℝ} (hδ : 0 < δ) (hM : 1 ≤ M) {S : StepMachine Formula ℤ → StepMachine (List Bool) Bool} (hS : SufficesSparse δ M S) {ℓ : ℕ}
    (hK : 72 / min (δ / (3 * M)) 1 ≤ levelK ℓ) (hE : Level.levelE ℓ ≤ min (δ / (3 * M)) 1 / 12) : Paper.DecidesInSteps (S (COUNTp ℓ)) δ := by sorry
