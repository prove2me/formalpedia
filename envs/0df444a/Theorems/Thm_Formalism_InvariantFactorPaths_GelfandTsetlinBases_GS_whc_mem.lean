-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_whc_mem
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:53.701802+00:00
-- url     : https://prove2.me/theorems/cba883e5-235a-4d6c-866a-9708b6390928
-- title:
--   GS: whc mem
-- statement:
--   The GS construction uses the whc mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L504-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L504-L508

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.whc_mem {G f : MvPolynomial (LVar ι ζ n) k} (hf : f ∈ genSpace isVec S G) (ν : Fin n → ℤ) :
    weightedHomogeneousComponent (wV isVec S) ν f ∈ genSpace isVec S G := by sorry
