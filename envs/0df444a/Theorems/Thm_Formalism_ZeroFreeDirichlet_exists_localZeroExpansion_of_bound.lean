-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exists_localZeroExpansion_of_bound
-- name    : Formalism.ZeroFreeDirichlet.exists_localZeroExpansion_of_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:47.881001+00:00
-- url     : https://prove2.me/theorems/e95f1068-1281-45ff-a3fa-9918406fb44e
-- title:
--   Zero Free Dirichlet: exists local Zero Expansion of bound
-- statement:
--   The Zero Free Dirichlet construction uses the exists local Zero Expansion of bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExistsLocalZeroExpansionOfBound.lean#L49-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ExistsLocalZeroExpansionOfBound.lean#L49-L180

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZeroFactor
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivBound
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ExistsLocalZeroExpansionOfBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.exists_localZeroExpansion_of_bound (f : ℂ → ℂ) (z₀ : ℂ) (r M : ℝ) (hr : 0 < r) (hM : 1 ≤ M)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ M * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ = 0 → 2 ≤ m ρ) ∧
      (∀ ρ ∈ Z, deriv f ρ ≠ 0 → m ρ = 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log M / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log M / r := by sorry
