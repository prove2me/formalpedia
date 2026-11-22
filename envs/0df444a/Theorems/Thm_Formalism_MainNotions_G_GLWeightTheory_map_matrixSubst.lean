-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_map_matrixSubst
-- name    : Formalism.MainNotions.G.GLWeightTheory.map_matrixSubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:40:41.666465+00:00
-- url     : https://prove2.me/theorems/843b85cc-fc74-453e-93b0-ddf7f1abfe1f
-- title:
--   GLWeight Theory: map matrix Subst
-- statement:
--   The GLWeight Theory construction uses the map matrix Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L78-L89

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

theorem Formalism.MainNotions.G.GLWeightTheory.map_matrixSubst (φ : R →+* B) (ψ : B →+* B') (m m' : Matrix (Fin n) (Fin n) B)
    (F : MvPolynomial (ι × Fin n) R) :
    MvPolynomial.map ψ (matrixSubst LL S φ m m' F) = matrixSubst LL S (ψ.comp φ) (m.map ψ) (m'.map ψ) F := by sorry
