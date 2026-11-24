-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_tw_coeff
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.tw_coeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:55.539394+00:00
-- url     : https://prove2.me/theorems/d58a7e60-5277-45ba-abea-45394612b7d9
-- title:
--   Gelfand Tsetlin Bases: tw coeff
-- statement:
--   The Gelfand Tsetlin Bases construction uses the tw coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L255-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L255-L262

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
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
variable {ι ζ : Type*} {n : ℕ} {L : Type*} [CommRing L]
variable (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.tw_coeff (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (H : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    (tw isVec S g gi last H).coeff j =
      sharpHom isVec S g gi
        (∑ e ∈ H.support.filter (fun e => wExp isVec S last e = j), monomial e (coeff e H)) := by sorry
