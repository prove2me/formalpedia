-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_Lo_le_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.Lo_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:54.327456+00:00
-- url     : https://prove2.me/theorems/4552189d-4bd2-465c-b124-6ed1b3d884b1
-- title:
--   Pieri: Lo le iff
-- statement:
--   The Pieri construction uses the Lo le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L127-L138

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.Lo_le_iff {n : ℕ} (μ ν : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    (∀ j, Lo μ l j ≤ ν j) ↔ (∀ j, μ j ≤ ν j) ∧ (∀ i : Fin n, l i ≤ ν i.castSucc) := by sorry
