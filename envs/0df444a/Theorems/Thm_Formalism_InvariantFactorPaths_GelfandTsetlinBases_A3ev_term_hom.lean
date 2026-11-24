-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3ev_term_hom
-- name    : Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.term_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:37.385694+00:00
-- url     : https://prove2.me/theorems/57441ba9-5abb-47cd-ae59-583162828e9f
-- title:
--   A3ev: term hom
-- statement:
--   The A3ev construction uses the term hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L186-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/JacobiPathWeights/JacobiMinorProofs/LemmaA2indepOf.lean#L186-L193

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

theorem Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3ev.term_hom (hW : PsiWeight) {L : Type} [CommRing L] {n N : ℕ} {isVec : ℕ → Bool} {B : ℕ → ℕ}
    {μ : ℕ → Fin n → ℤ} (hp : IsPath n isVec B μ N)
    {F : Finset ℤ} (hF : Cols isVec μ N F) (g gi : Matrix (Fin n) (Fin n) L)
    (I : ℤ → Finset (Fin n)) {I' : ℤ → Finset (Fin n)} (hI' : IsIndex (μ N) I') :
    IsWeightedHomogeneous (torusW isVec) (term isVec μ N F g gi I I') (idxWeight I') := by sorry
