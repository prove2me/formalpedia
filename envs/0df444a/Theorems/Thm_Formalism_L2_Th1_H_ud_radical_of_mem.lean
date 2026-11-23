-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_ud_radical_of_mem
-- name    : Formalism.L2.Th1.H.ud_radical_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:29:11.571723+00:00
-- url     : https://prove2.me/theorems/00e1df3f-cfb5-4792-856a-8ade6c25cd7e
-- title:
--   H: ud radical of mem
-- statement:
--   The H construction uses the ud radical of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyPhaseQuadratic.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyPhaseQuadratic.lean#L145-L151

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}

theorem Formalism.L2.Th1.H.ud_radical_of_mem (h : UnitaryData H Λ α δ Ae) {x : V} (hx : x ∈ latA Λ δ Ae) {x' : V}
    (hx' : x' ∈ Λ) : bC H Ae x x' = 1 := by sorry
