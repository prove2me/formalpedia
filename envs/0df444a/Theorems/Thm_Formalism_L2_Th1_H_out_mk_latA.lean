-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_out_mk_latA
-- name    : Formalism.L2.Th1.H.out_mk_latA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:28:45.555877+00:00
-- url     : https://prove2.me/theorems/b39ea540-12cd-4589-900d-c12dd6a15cd6
-- title:
--   H: out mk lat A
-- statement:
--   The H construction uses the out mk lat A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyPhaseQuadratic.lean#L302-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyPhaseQuadratic.lean#L302-L315

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

theorem Formalism.L2.Th1.H.out_mk_latA (x : Λ) : ∃ k ∈ latA Λ δ Ae,
    ((Quotient.out (QuotientAddGroup.mk x : Λ ⧸ (latA Λ δ Ae).addSubgroupOf Λ) : Λ) : V)
      = (x : V) + k := by sorry
