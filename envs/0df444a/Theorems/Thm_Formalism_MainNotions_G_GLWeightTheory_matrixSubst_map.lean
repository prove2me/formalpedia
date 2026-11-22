-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_map
-- name    : Formalism.MainNotions.G.GLWeightTheory.matrixSubst_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:16.67704+00:00
-- url     : https://prove2.me/theorems/55ab8fca-3671-4453-bc3b-889300618ea1
-- title:
--   GLWeight Theory: matrix Subst map
-- statement:
--   The GLWeight Theory construction uses the matrix Subst map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L103-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L103-L105

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

theorem Formalism.MainNotions.G.GLWeightTheory.matrixSubst_map (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (F : MvPolynomial (ι × Fin n) R) :
    matrixSubst LL S (RingHom.id B) m m' (MvPolynomial.map φ F) = matrixSubst LL S φ m m' F := by sorry
