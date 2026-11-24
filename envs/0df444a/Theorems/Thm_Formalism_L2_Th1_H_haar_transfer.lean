-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_haar_transfer
-- name    : Formalism.L2.Th1.H.haar_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:17.801491+00:00
-- url     : https://prove2.me/theorems/3e12eaea-f198-48d3-9b4a-79a3f3caa368
-- title:
--   H: haar transfer
-- statement:
--   The H construction uses the haar transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyGaussianIntegral.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyGaussianIntegral.lean#L44-L59

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

theorem Formalism.L2.Th1.H.haar_transfer {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {n : Type*} [Fintype n] (Φ : (n → ℂ) ≃ₗ[ℂ] V) :
    ∃ κ : ℝ, ∀ f : V → ℂ, (Integrable (fun w => f (Φ w)) → Integrable f μ) ∧
      ∫ z, f z ∂μ = (κ : ℂ) * ∫ w, f (Φ w) := by sorry
