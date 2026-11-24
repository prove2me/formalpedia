-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_C_one_col
-- name    : Formalism.MainNotions.G.GLWeightTheory.sum_C_one_col
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:18.175288+00:00
-- url     : https://prove2.me/theorems/1a615ab4-23df-4a02-be15-ae0573d85db9
-- title:
--   GLWeight Theory: sum C one col
-- statement:
--   The GLWeight Theory construction uses the sum C one col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean#L28-L34

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_TwistSubEqMatrixSubst
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_RootWeights_MatrixSubstTransvectionX
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
variable {R B : Type*} [CommRing R] [CommRing B] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
  (φ : R →+* B) (a b : Fin n) (t : B)

theorem Formalism.MainNotions.G.GLWeightTheory.sum_C_one_col (l : ι) (c : Fin n) :
    ∑ b' : Fin n, C ((1 : Matrix (Fin n) (Fin n) B) b' c) * (X (l, b') : MvPolynomial (ι × Fin n) B) = X (l, c) := by sorry
