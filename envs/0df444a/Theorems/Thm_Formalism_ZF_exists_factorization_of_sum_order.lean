-- Prove2me | Theorems.Thm_Formalism_ZF_exists_factorization_of_sum_order
-- name    : Formalism.ZF.exists_factorization_of_sum_order
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:55.18334+00:00
-- url     : https://prove2.me/theorems/3a62056d-6c71-4b1c-9e07-971422035aac
-- title:
--   ZF: exists factorization of sum order
-- statement:
--   The ZF construction uses the exists factorization of sum order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZeroFactor.lean#L18-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/ZeroFactor.lean#L18-L118

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.exists_factorization_of_sum_order (z₀ : ℂ) (r R₁ : ℝ) (hR : R₁ < r) :
    ∀ N : ℕ, ∀ (f : ℂ → ℂ) (Z : Finset ℂ), DifferentiableOn ℂ f (Metric.closedBall z₀ r) →
      (∀ ρ ∈ Z, ρ ∈ Metric.closedBall z₀ R₁) →
      (∀ z ∈ Metric.closedBall z₀ R₁, f z = 0 → z ∈ Z) →
      (∀ ρ ∈ Z, analyticOrderAt f ρ ≠ ⊤) →
      ∑ ρ ∈ Z, analyticOrderNatAt f ρ = N →
      ∃ h : ℂ → ℂ, DifferentiableOn ℂ h (Metric.closedBall z₀ r) ∧
        (∀ z ∈ Metric.closedBall z₀ R₁, h z ≠ 0) ∧
        ∀ z ∈ Metric.closedBall z₀ r, f z = (∏ ρ ∈ Z, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by sorry
