-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn0_mem_rad
-- name    : Formalism.L2.Th1.H.IsQuadFn0.mem_rad
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:13.730683+00:00
-- url     : https://prove2.me/theorems/684d48a7-1f71-4134-b189-01ccf6575cea
-- title:
--   Is Quad Fn0: mem rad
-- statement:
--   The Is Quad Fn0 construction uses the mem rad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L195-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GapStatement.lean#L195-L195

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

theorem Formalism.L2.Th1.H.IsQuadFn0.mem_rad (h : IsQuadFn0 φ b) (x : M) : x ∈ h.rad ↔ ∀ y, b x y = 1 := by sorry
