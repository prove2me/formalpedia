-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_b_neg_right
-- name    : Formalism.L2.Th1.H.IsQuadFn.b_neg_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:12.772141+00:00
-- url     : https://prove2.me/theorems/3e1bee8f-e93d-41bf-9b8f-dc300e1d7d41
-- title:
--   Is Quad Fn: b neg right
-- statement:
--   The Is Quad Fn construction uses the b neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L50-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L50-L51

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

theorem Formalism.L2.Th1.H.IsQuadFn.b_neg_right (h : IsQuadFn φ b) (x y : M) : b x (-y) = (b x y)⁻¹ := by sorry
