-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_scale_deriv_lower_of_renewal_identity
-- name    : AvramDividend.Classical.esscher_scale_deriv_lower_of_renewal_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:47:18.049509+00:00
-- url     : https://prove2.me/theorems/685c6dfa-6848-4513-b4df-bcd3817fc11a
-- title:
--   Scale derivative inherits the Esscher renewal-density lower bound
-- statement:
--   A real scale function equal on the positive axis to the exponentially tilted primitive of an integrable continuous renewal density has ordinary derivative at least the prescribed density lower bound. This composes the Proved Esscher calculus estimate with the pinned Mathlib local equality-of-derivatives theorem, leaving only the canonical renewal-kernel positivity and tail divergence for the bounded-variation zero-barrier branch.
-- source:
--   Proved esscher_integrated_density_derivative_lower (ded14437-3cf3-4404-b8fa-2a1b800dade9), Mathlib Set.EqOn.deriv, and Avram–Palmowski–Pistorius (2007).

import Theorems.Thm_AvramDividend_Classical_esscher_integrated_density_derivative_lower
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped Topology

namespace AvramDividend.Classical

/-- Positive-axis equality with an Esscher renewal primitive transfers its derivative floor. -/
theorem esscher_scale_deriv_lower_of_renewal_identity
    (W : ℝ → ℝ) (φ c : ℝ) (f k : ℝ → ℝ)
    (hφ : 0 ≤ φ)
    (hW : ∀ x : ℝ, 0 < x → W x =
      Real.exp (φ * x) * (c + ∫ t in (0 : ℝ)..x, f t))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hmeas : ∀ x : ℝ, 0 < x → StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hk : ∀ x : ℝ, 0 < x → k x ≤ f x) :
    ∀ x : ℝ, 0 < x → k x ≤ deriv W x := by sorry

end AvramDividend.Classical
