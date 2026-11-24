-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_prod
-- name    : Formalism.InvariantFactorPaths.G7.biLe_prod
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:18.956851+00:00
-- url     : https://prove2.me/theorems/db2d8211-5154-4050-8fd0-6eb3f7e5927f
-- title:
--   G7: bi Le prod
-- statement:
--   The G7 construction uses the bi Le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L253-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L253-L262

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_MinorProdBlockDegree
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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
variable {K ι κ : Type} [Field K]

theorem Formalism.InvariantFactorPaths.G7.biLe_prod {α : Type*} (s : Finset α) (N : α → ι →₀ ℕ)
    (W : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, BiLe (N a) (W a)) :
    BiLe (∑ a ∈ s, N a) (∏ a ∈ s, W a) := by sorry
