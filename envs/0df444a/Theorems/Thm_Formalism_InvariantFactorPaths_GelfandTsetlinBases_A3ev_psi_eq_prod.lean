-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_psi_eq_prod
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.psi_eq_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:49.176808+00:00
-- url     : https://prove2.me/theorems/86cc6da5-987d-4695-acd5-9192e9b0254e
-- title:
--   A3ev: psi eq prod
-- statement:
--   The A3ev construction uses the psi eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L38-L48

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.psi_eq_prod (R : Type) [CommRing R] {n N : ℕ} {isVec : ℕ → Bool} {μ : ℕ → Fin n → ℤ}
    {F : Finset ℤ} (hF : Cols isVec μ N F) {I : ℤ → Finset (Fin n)} (hI : IsIndex (μ N) I) :
    psiPath R isVec μ N I =
      ∏ c ∈ F, pathWord isVec μ c (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) N (I c) := by sorry
