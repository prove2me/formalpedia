-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_twistSub_eq_matrixSubst
-- name    : Formalism.MainNotions.G.GLWeightTheory.twistSub_eq_matrixSubst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:55:07.472577+00:00
-- url     : https://prove2.me/theorems/1a2a8e93-0119-4fe6-b565-e51d9ce736f5
-- title:
--   GLWeight Theory: twist Sub eq matrix Subst
-- statement:
--   The GLWeight Theory construction uses the twist Sub eq matrix Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L26-L27

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

theorem Formalism.MainNotions.G.GLWeightTheory.twistSub_eq_matrixSubst (j : Fin n) :
    twistSub (R := R) LL S j = matrixSubst LL S (coefL R n) (twistMat R n j 1) (twistMat R n j (-1)) := by sorry
