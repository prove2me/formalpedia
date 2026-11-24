-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_genH_support
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.genH_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:54.595219+00:00
-- url     : https://prove2.me/theorems/2c601763-6de6-4312-821f-77f654652611
-- title:
--   GS: gen H support
-- statement:
--   The GS construction uses the gen H support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L568-L583
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L568-L583

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_GenSpaceFacts
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS
variable {k : Type*} [Field k] {ι ζ : Type*} {n : ℕ} (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.genH_support (G : MvPolynomial (LVar ι ζ n) k) (e : LVar ι ζ n →₀ ℕ) :
    e ∈ (genH isVec S G).support ↔ e ∈ (rho isVec S G).support := by sorry
