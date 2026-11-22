-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjAct_C
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:23.469083+00:00
-- url     : https://prove2.me/theorems/90b402a8-ec20-4844-8608-185872c3bc47
-- title:
--   Gelfand Tsetlin Bases: conj Act C
-- statement:
--   The Gelfand Tsetlin Bases construction uses the conj Act C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L178-L180

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_C {k : Type*} [CommRing k] (φ : k →+* L) (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (c : k) :
    conjAct (ζ := ζ) φ isVec S g gi last (C c) = cc _ L (φ c) := by sorry
