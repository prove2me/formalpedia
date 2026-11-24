-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_MinorDeterminantBasis_psi_support
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.psi_support
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:32.05426+00:00
-- url     : https://prove2.me/theorems/5b298d83-86f4-4977-b07c-954f5e4940fd
-- title:
--   Minor Determinant Basis: psi support
-- statement:
--   The Minor Determinant Basis construction uses the psi support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathBasisOfCount.lean#L170-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/PathBasisOfCount.lean#L170-L175

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathBasisOfCount
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.MinorDeterminantBasis.psi_support (hr : PolBRank) {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ} {μ : ℕ → Fin n → ℤ}
    {I : ℤ → Finset (Fin n)} (hμ : IsPath n isVec B μ N) (hI : IsIndex (μ N) I) :
    ∀ d ∈ (psiPath ℤ isVec μ N I).support, d ∈ expSet n N B := by sorry
