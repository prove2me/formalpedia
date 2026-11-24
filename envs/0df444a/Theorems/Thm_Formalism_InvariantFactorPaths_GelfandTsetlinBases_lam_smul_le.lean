-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_lam_smul_le
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.lam_smul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:50.169937+00:00
-- url     : https://prove2.me/theorems/d500f93b-e7dc-4d49-8e36-ecedfd96f7a3
-- title:
--   Gelfand Tsetlin Bases: lam smul le
-- statement:
--   The Gelfand Tsetlin Bases construction uses the lam smul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L440-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/ExistsSuppOfEvalNe.lean#L440-L444

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
variable {ι ζ : Type*} {n : ℕ} {k : Type*} [Field k] (isVec : ι → Bool) (S : Set ι) [DecidablePred (· ∈ S)]

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.lam_smul_le (M : WithBot ℤ) (c : k) (G : MvPolynomial (LVar ι ζ n) k) (h : lam1S isVec S G ≤ M) :
    lam1S isVec S (c • G) ≤ M := by sorry
