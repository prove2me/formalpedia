-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_pow4
-- name    : Formalism.L2.Th1.H.IsQuadFn.pow4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:44.677669+00:00
-- url     : https://prove2.me/theorems/a579c6c1-3de1-4122-938b-95bd2cb86468
-- title:
--   Is Quad Fn: pow4
-- statement:
--   The Is Quad Fn construction uses the pow4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L134-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L134-L150

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

theorem Formalism.L2.Th1.H.IsQuadFn.pow4 (h : IsQuadFn φ b) :
    IsQuadFn (fun v : Fin 4 → M => ∏ i, φ (v i)) (fun v w => ∏ i, b (v i) (w i)) := by sorry
