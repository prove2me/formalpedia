-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conj_mem_supp
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.conj_mem_supp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:12.54573+00:00
-- url     : https://prove2.me/theorems/4f450141-50eb-4b0a-8091-907fc88802b4
-- title:
--   Gelfand Tsetlin Bases: conj mem supp
-- statement:
--   The Gelfand Tsetlin Bases construction uses the conj mem supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L352-L359
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L352-L359

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
variable {ι ζ : Type*} {n : ℕ}

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.conj_mem_supp {L : Type*} [CommRing L] (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] {g gi : Matrix (Fin n) (Fin n) L} (h : g * gi = 1) (h' : gi * g = 1) (last : Bool)
    (G : MvPolynomial (LVar ι ζ n) L) (j : ℤ) :
    j ∈ (conjAct (RingHom.id L) isVec S g gi last G).coeff.support ↔
      ∃ e ∈ (sharpHom isVec S gi g G).support, wExp isVec S last e = j := by sorry
