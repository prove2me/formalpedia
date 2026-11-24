-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_strip2_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.strip2_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:04.664916+00:00
-- url     : https://prove2.me/theorems/6e9983b0-0538-4d70-8d86-21bdfc4f3770
-- title:
--   Pieri: strip2 iff
-- statement:
--   The Pieri construction uses the strip2 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L164-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L164-L175

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.strip2_iff {n : ℕ} (μ ν : Fin (n + 1) → ℤ) :
    (∀ m m' : Fin (n + 1), m.val + 1 = m'.val → ν m' ≤ μ m) ↔ ∀ i : Fin n, ν i.succ ≤ μ i.castSucc := by sorry
