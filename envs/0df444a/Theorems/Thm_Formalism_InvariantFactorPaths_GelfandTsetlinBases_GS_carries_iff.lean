-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_GS_carries_iff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.carries_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:59.072303+00:00
-- url     : https://prove2.me/theorems/8abc050e-f79d-4493-8b34-0b52219ebd98
-- title:
--   GS: carries iff
-- statement:
--   The GS construction uses the carries iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L325-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/GenSpace.lean#L325-L328

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.GS.carries_iff (G : MvPolynomial (LVar ι ζ n) k) (N : Submodule k (MvPolynomial (LVar ι ζ n) k)) :
    Carries isVec S G N ↔ slSpace (k := k) (rho isVec S G) ≤ N := by sorry
