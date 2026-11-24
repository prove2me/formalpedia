-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn0_phi_rad
-- name    : Formalism.L2.Th1.H.IsQuadFn0.phi_rad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:45.57332+00:00
-- url     : https://prove2.me/theorems/be83f5c8-3f57-4706-9173-49860178194a
-- title:
--   Is Quad Fn0: phi rad
-- statement:
--   The Is Quad Fn0 construction uses the phi rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L197-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L197-L207

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_GaussDegenerate
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaussSumEighthPower
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GapStatement
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
open SemicharacterExponentialLemmas
open Formalism.L2.Th1.H.IsQuadFn0
variable {M : Type*} [AddCommGroup M] {φ : M → ℂ} {b : M → M → ℂ}

theorem Formalism.L2.Th1.H.IsQuadFn0.phi_rad [Fintype M] (h : IsQuadFn0 φ b) (hS : ∑ x, φ x ≠ 0) {r : M} (hr : r ∈ h.rad) :
    φ r = 1 := by sorry
