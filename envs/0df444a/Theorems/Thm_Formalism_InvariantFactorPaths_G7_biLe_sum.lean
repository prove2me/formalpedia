-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_biLe_sum
-- name    : Formalism.InvariantFactorPaths.G7.biLe_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:29:29.921717+00:00
-- url     : https://prove2.me/theorems/0a39482d-b8f8-4bb6-99c1-64c7c7f4428e
-- title:
--   G7: bi Le sum
-- statement:
--   The G7 construction uses the bi Le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L128-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L128-L137

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

theorem Formalism.InvariantFactorPaths.G7.biLe_sum {α : Type*} {n0 : ι →₀ ℕ} (s : Finset α)
    (W : α → MvPolynomial κ (MvPolynomial ι K)) (h : ∀ a ∈ s, BiLe n0 (W a)) :
    BiLe n0 (∑ a ∈ s, W a) := by sorry
