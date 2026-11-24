-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Count_sum_succs
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.sum_succs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:53.729806+00:00
-- url     : https://prove2.me/theorems/44d862fd-0b5e-444f-b611-40b52c787ff8
-- title:
--   Count: sum succs
-- statement:
--   The Count construction uses the sum succs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/NormIndexCountBound.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/NormIndexCountBound.lean#L48-L53

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.Count.sum_succs (hP : GTPieri) {n : ℕ} (v : Bool) (b : ℕ) (μ : Fin n → ℤ) (hμ : Antitone μ) :
    ∑ ν ∈ succs v b μ, dGT n ν = dGT n μ * (n + b - 1).choose b := by sorry
