-- Prove2me | Theorems.Thm_DeletionCode_PaperProbability_obstructions_are_rare
-- name    : DeletionCode.PaperProbability.obstructions_are_rare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:04:49.881985+00:00
-- url     : https://prove2.me/theorems/4fb917ee-9775-4958-a69d-05786bc52427
-- title:
--   Paper Probability: obstructions are rare
-- statement:
--   The obstruction proposition with the actual paper parameters and all
--   large-n side conditions derived, for every allowed number of labels.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L78-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/PaperProbability.lean#L78-L87

import Definitions.Def_DeletionCode_NonseparatedFamily
import Definitions.Def_DeletionCode_ObstructionBound
import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_PaperProbability
set_option autoImplicit true
open DeletionCode DeletionCode.PaperProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleUniform
open ExceptionalCountArithmetic ExceptionalProbability ObstructionProbability
open scoped ENNReal

theorem DeletionCode.PaperProbability.obstructions_are_rare (t : ℕ) (ht : 2 ≤ t) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q : ℕ,
      8 * ObstructionBound.scale t n (PaperParameters.k n) ≤ Q → ∀ x : Bits n,
        KUnique (padBits x) n (PaperParameters.k n) →
          realWeights (Gram (PaperParameters.L n)) (obstructionEvent t (PaperParameters.k n) Q x) ≤
            ENNReal.ofReal (1 / 12 : ℝ) := by sorry
