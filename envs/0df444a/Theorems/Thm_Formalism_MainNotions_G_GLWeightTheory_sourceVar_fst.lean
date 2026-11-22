-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sourceVar_fst
-- name    : Formalism.MainNotions.G.GLWeightTheory.sourceVar_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:33:55.4068+00:00
-- url     : https://prove2.me/theorems/3daa1657-e2ae-4bbf-87f0-98b55c19a3a7
-- title:
--   GLWeight Theory: source Var fst
-- statement:
--   The GLWeight Theory construction uses the source Var fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean#L19-L21

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

theorem Formalism.MainNotions.G.GLWeightTheory.sourceVar_fst {ι : Type*} {n : ℕ} (LL : Letters ι) (a b : Fin n) (l : ι) : (sourceVar LL a b l).1 = l := by sorry
