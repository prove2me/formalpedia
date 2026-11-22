-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_GLWeightTheory_sum_single_sourceVar_apply
-- name    : Formalism.MainNotions.G.GLWeightTheory.sum_single_sourceVar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:01:19.230814+00:00
-- url     : https://prove2.me/theorems/4b41a11c-8d05-4407-9da9-b888670b5772
-- title:
--   GLWeight Theory: sum single source Var apply
-- statement:
--   The GLWeight Theory construction uses the sum single source Var apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean#L86-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/RootWeights/MatrixSubstTransvectionX.lean#L86-L99

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
variable {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (a b : Fin n)
open Classical

theorem Formalism.MainNotions.G.GLWeightTheory.sum_single_sourceVar_apply (c : ι → ℕ) (v : ι × Fin n) :
    (∑ l : ι, Finsupp.single (sourceVar LL a b l) (c l)) v = if v = sourceVar LL a b v.1 then c v.1 else 0 := by sorry
