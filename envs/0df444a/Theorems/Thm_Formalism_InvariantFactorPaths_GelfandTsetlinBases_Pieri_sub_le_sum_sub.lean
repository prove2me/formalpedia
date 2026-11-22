-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sub_le_sum_sub
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sub_le_sum_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:50.775646+00:00
-- url     : https://prove2.me/theorems/acfa6407-ab3e-4c32-a4d6-e272e0814d71
-- title:
--   Pieri: sub le sum sub
-- statement:
--   The Pieri construction uses the sub le sum sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L13-L17

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sub_le_sum_sub {n : ℕ} (ν μ : Fin n → ℤ) (h : ∀ m, μ m ≤ ν m) (i : Fin n) :
    ν i - μ i ≤ ∑ m, ν m - ∑ m, μ m := by sorry
