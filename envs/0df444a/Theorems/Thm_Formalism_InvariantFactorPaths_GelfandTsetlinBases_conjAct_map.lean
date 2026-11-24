-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_conjAct_map
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:44.327833+00:00
-- url     : https://prove2.me/theorems/241a2fe4-286a-451d-afe6-fabc3c5ac94d
-- title:
--   Gelfand Tsetlin Bases: conj Act map
-- statement:
--   The Gelfand Tsetlin Bases construction uses the conj Act map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L321-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L321-L331

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.conjAct_map {k L : Type*} [CommRing k] [CommRing L] (φ : k →+* L) (isVec : ι → Bool) (S : Set ι)
    [DecidablePred (· ∈ S)] (g gi : Matrix (Fin n) (Fin n) L) (last : Bool) (G : MvPolynomial (LVar ι ζ n) k) :
    conjAct φ isVec S g gi last G = conjAct (RingHom.id L) isVec S g gi last (map φ G) := by sorry
