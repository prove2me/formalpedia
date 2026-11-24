-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_sum_sq_of_anti
-- name    : Formalism.L2.Th1.H.IsQuadFn.sum_sq_of_anti
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:57.464374+00:00
-- url     : https://prove2.me/theorems/449ff156-0041-4d45-95c1-5292fc778559
-- title:
--   Is Quad Fn: sum sq of anti
-- statement:
--   The Is Quad Fn construction uses the sum sq of anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L79-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L79-L132

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

theorem Formalism.L2.Th1.H.IsQuadFn.sum_sq_of_anti {P : Type*} [AddCommGroup P] [Fintype P] {Φ : P → ℂ} {B : P → P → ℂ}
    (h : IsQuadFn Φ B) (T : P →+ P) (hT : ∀ v, Φ v * Φ (T v) = 1) :
    (∑ v, Φ v) ^ 2 = (Fintype.card P : ℂ) := by sorry
