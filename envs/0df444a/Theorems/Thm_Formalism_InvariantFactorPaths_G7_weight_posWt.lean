-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_weight_posWt
-- name    : Formalism.InvariantFactorPaths.G7.weight_posWt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:48.644801+00:00
-- url     : https://prove2.me/theorems/c930e00a-ee0d-422c-aa68-d0924c2cdd2d
-- title:
--   G7: weight pos Wt
-- statement:
--   The G7 construction uses the weight pos Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L297-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/MinorProdBlockDegree.lean#L297-L327

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
variable {K σ : Type} [Field K] [DecidableEq σ] {r0 r1 : ℕ}

theorem Formalism.InvariantFactorPaths.G7.weight_posWt (s : σ) (n : σ × Fin r0 × Fin r1 →₀ ℕ) :
    Finsupp.weight (posWt r0 r1 s) n = ∑ x : Fin r0 × Fin r1, n (s, x) := by sorry
