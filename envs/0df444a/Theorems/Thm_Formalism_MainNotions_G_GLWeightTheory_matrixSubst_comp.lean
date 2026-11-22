-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_comp
-- name    : Formalism.MainNotions.G.GLWeightTheory.matrixSubst_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:13.871982+00:00
-- url     : https://prove2.me/theorems/894af819-72be-4847-9434-d4d3e1b166f3
-- title:
--   GLWeight Theory: matrix Subst comp
-- statement:
--   The GLWeight Theory construction uses the matrix Subst comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L41-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L41-L76

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory
open Formalism.MainNotions.G
variable {R B B' : Type*} [CommRing R] [CommRing B] [CommRing B'] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)

theorem Formalism.MainNotions.G.GLWeightTheory.matrixSubst_comp (φ : R →+* B) (m1 m1' m2 m2' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m1 m1' (matrixSubst LL S φ m2 m2' F) = matrixSubst LL S φ (m1 * m2) (m2' * m1') F := by sorry
