-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_isLat_inf
-- name    : Formalism.L2.Th1.H.isLat_inf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:25.83533+00:00
-- url     : https://prove2.me/theorems/3ddd92ef-3324-4739-9533-71bd9b094af6
-- title:
--   H: is Lat inf
-- statement:
--   The H construction uses the is Lat inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexEqAbsDetReal.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/RelIndexEqAbsDetReal.lean#L81-L96

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_RelIndexEqAbsDetReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Module
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.isLat_inf {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {Λ Λ₁ : AddSubgroup V}
    (hL : IsLat Λ) (hi : Λ₁.relIndex Λ ≠ 0) : IsLat (Λ ⊓ Λ₁) := by sorry
