-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_gauss_pi
-- name    : Formalism.L2.Th1.H.gauss_pi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:25.995577+00:00
-- url     : https://prove2.me/theorems/8c037a6c-b59c-4367-93bc-500feca93d97
-- title:
--   H: gauss pi
-- statement:
--   The H construction uses the gauss pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyGaussianIntegral.lean#L24-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyGaussianIntegral.lean#L24-L42

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyGaussianIntegral
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
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H

theorem Formalism.L2.Th1.H.gauss_pi {n : Type*} [Fintype n] (l : n → ℂ) (hl : ∀ i, 0 < (l i).re) :
    Integrable (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ w : n → ℂ, Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = (∏ i, l i)⁻¹ := by sorry
