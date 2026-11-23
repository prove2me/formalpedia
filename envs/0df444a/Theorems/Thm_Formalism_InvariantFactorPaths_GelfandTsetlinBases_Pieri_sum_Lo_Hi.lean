-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Pieri_sum_Lo_Hi
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sum_Lo_Hi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:47.924126+00:00
-- url     : https://prove2.me/theorems/6c374459-820f-4d82-a4a9-7a28dd248936
-- title:
--   Pieri: sum Lo Hi
-- statement:
--   The Pieri construction uses the sum Lo Hi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/AntitoneOfMemGtBox.lean#L117-L125

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Pieri.sum_Lo_Hi {n : ℕ} (μ : Fin (n + 1) → ℤ) (l : Fin n → ℤ) :
    ∑ j, Lo μ l j + ∑ i, Hi μ l i = ∑ j, μ j + ∑ i, l i := by sorry
