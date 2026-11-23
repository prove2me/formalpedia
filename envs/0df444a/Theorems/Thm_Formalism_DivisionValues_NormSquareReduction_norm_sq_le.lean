-- Prove2me | Theorems.Thm_Formalism_DivisionValues_NormSquareReduction_norm_sq_le
-- name    : Formalism.DivisionValues.NormSquareReduction.norm_sq_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:34.285822+00:00
-- url     : https://prove2.me/theorems/0e952bc5-17f4-4b14-9094-d865b4fa7dee
-- title:
--   Norm Square Reduction: norm sq le
-- statement:
--   The Norm Square Reduction construction uses the norm sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionThirdStepMean.lean#L17-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ReductionThirdStepMean.lean#L17-L81

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementACE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.NormSquareReduction
variable {Q E : Type} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem Formalism.DivisionValues.NormSquareReduction.norm_sq_le (ι : Q →ₗ[ℂ] E) {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule ℂ Q)
    (hsup : (⨆ p, Qp p) = ⊤) (s : Ix → ℝ) (smin : ℝ) (hs : ∀ p, smin ≤ s p)
    (hι : ∀ p, ∀ x ∈ Qp p, ∀ y : Q, ⟪ι x, ι y⟫_ℂ = (s p : ℂ) * ⟪x, y⟫_ℂ) (F : Q) :
    smin * ‖F‖ ^ 2 ≤ ‖ι F‖ ^ 2 := by sorry
