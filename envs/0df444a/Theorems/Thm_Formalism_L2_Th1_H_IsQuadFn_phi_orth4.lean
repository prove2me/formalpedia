-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_IsQuadFn_phi_orth4
-- name    : Formalism.L2.Th1.H.IsQuadFn.phi_orth4
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:05.802911+00:00
-- url     : https://prove2.me/theorems/df6b0dff-de83-486e-b8f5-cda2f2d49c02
-- title:
--   Is Quad Fn: phi orth4
-- statement:
--   The Is Quad Fn construction uses the phi orth4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L70-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/GaussSumEighthPower.lean#L70-L77

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

theorem Formalism.L2.Th1.H.IsQuadFn.phi_orth4 (h : IsQuadFn φ b) (x₀ x₁ x₂ x₃ : M) (h01 : b x₀ x₁ = 1) (h02 : b x₀ x₂ = 1)
    (h03 : b x₀ x₃ = 1) (h12 : b x₁ x₂ = 1) (h13 : b x₁ x₃ = 1) (h23 : b x₂ x₃ = 1)
    (k₀ k₁ k₂ k₃ : ℕ) :
    φ (k₀ • x₀ + k₁ • x₁ + k₂ • x₂ + k₃ • x₃)
      = φ x₀ ^ (k₀ ^ 2) * φ x₁ ^ (k₁ ^ 2) * φ x₂ ^ (k₂ ^ 2) * φ x₃ ^ (k₃ ^ 2) := by sorry
