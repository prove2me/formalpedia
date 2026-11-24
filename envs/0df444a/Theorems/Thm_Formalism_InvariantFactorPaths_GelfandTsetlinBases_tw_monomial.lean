-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_tw_monomial
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.tw_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:33.509545+00:00
-- url     : https://prove2.me/theorems/452c3519-cf20-4768-9a2f-dd98dafac365
-- title:
--   Gelfand Tsetlin Bases: tw monomial
-- statement:
--   The Gelfand Tsetlin Bases construction uses the tw monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L243-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L243-L253

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.tw_monomial (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (e : LVar ι ζ n →₀ ℕ) (c : L) :
    tw isVec S g gi last (monomial e c) =
      LaurentPolynomial.T (wExp isVec S last e) * LaurentPolynomial.C (sharpHom isVec S g gi (monomial e c)) := by sorry
