-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_matrixSubst_X
-- name    : Formalism.MainNotions.G.GLWeightTheory.matrixSubst_X
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:43.827435+00:00
-- url     : https://prove2.me/theorems/523c31c6-aae6-4da2-afb5-8a43bc7a5da6
-- title:
--   GLWeight Theory: matrix Subst X
-- statement:
--   The GLWeight Theory construction uses the matrix Subst X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L34-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/TwistSubEqMatrixSubst.lean#L34-L39

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
open Classical

theorem Formalism.MainNotions.G.GLWeightTheory.matrixSubst_X (φ : R →+* B) (m m' : Matrix (Fin n) (Fin n) B) (v : ι × Fin n) :
    matrixSubst LL S φ m m' (X v) = if v.1 ∈ S then
      (if LL.vec v.1 then ∑ b : Fin n, MvPolynomial.C (m b v.2) * X (v.1, b)
       else ∑ b : Fin n, MvPolynomial.C (m' v.2 b) * X (v.1, b))
    else X v := by sorry
