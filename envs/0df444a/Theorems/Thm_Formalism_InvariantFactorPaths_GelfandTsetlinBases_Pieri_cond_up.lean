-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_cond_up
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.cond_up
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:41.872287+00:00
-- url     : https://prove2.me/theorems/6223a6bb-f9b9-4d7a-8338-f98345e1541b
-- title:
--   Pieri: cond up
-- statement:
--   The Pieri construction uses the cond up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L177-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L177-L187

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_AntitoneOfMemGtBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.cond_up {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) (b : ℕ) :
    (HStrip ν μ b ∧ l ∈ gtBox ν) ↔
      (∀ j, Lo μ l j ≤ ν j) ∧ (∀ i, ν i.succ ≤ Hi μ l i) ∧ ∑ j, ν j - ∑ j, μ j = (b : ℤ) := by sorry
