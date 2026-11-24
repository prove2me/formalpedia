-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_nsmul_left
-- name    : Formalism.L2.Th1.H.IsQuadFn.b_nsmul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:17.398728+00:00
-- url     : https://prove2.me/theorems/4f29e3f9-164c-487a-afa3-8b8439abeac8
-- title:
--   Is Quad Fn: b nsmul left
-- statement:
--   The Is Quad Fn construction uses the b nsmul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L35-L38

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.L2.Th1.H.IsQuadFn
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}

theorem Formalism.L2.Th1.H.IsQuadFn.b_nsmul_left (h : IsQuadFn φ b) (k : ℕ) (x y : M) : b (k • x) y = b x y ^ k := by sorry
