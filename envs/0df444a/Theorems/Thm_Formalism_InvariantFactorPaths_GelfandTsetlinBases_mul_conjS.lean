-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_mul_conjS
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.mul_conjS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:34.514773+00:00
-- url     : https://prove2.me/theorems/3e1199ba-c95c-4e1f-b779-f69e2c813406
-- title:
--   Gelfand Tsetlin Bases: mul conj S
-- statement:
--   The Gelfand Tsetlin Bases construction uses the mul conj S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L166-L169

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.mul_conjS (τ : Type*) {g gi : Matrix (Fin n) (Fin n) L} (h : gi * g = 1) (last : Bool) (e : ℤ) :
    gi.map (cc τ L) * conjS τ g gi last e = diagS (MvPolynomial τ L) n last e * gi.map (cc τ L) := by sorry
