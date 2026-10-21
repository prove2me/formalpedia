-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_postPayment_candidate_bounded_finite_cap
-- name    : AvramDividend.Classical.discounted_postPayment_candidate_bounded_finite_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T08:43:50.49376+00:00
-- url     : https://prove2.me/theorems/be0beb7d-f5f4-4329-94a1-41196785eb02
-- title:
--   Discounted terminal candidate values are uniformly bounded and nonnegative at finite cap
-- statement:
--   At a finite real cap c≥0 with x in its admissible cap and under the exact local verification HJB assumptions with q>0, there is a deterministic B≥0 such that every sample path and every finite time satisfies 0≤e^(-qt)w(x+X_t−D_{t+})≤B. The independently Proved local_verification_postPayment_terminal_nonnegative supplies the lower bound, and the pending finite-cap uniform upper bound theorem supplies w(U_t+)≤B. The discount multiplier e^(-qt) lies in (0,1] since q>0, t≥0. Consequently bounded discounted terminal residuals hold pathwise, including after ruin. This is a bounded-terminal-process prerequisite for localisation, not optional sampling or the Levy-Ito identity itself.
-- source:
--   Dependency-gated: only publish after capped_postPayment_candidate_uniform_upper_bound_finite_cap is Proved. Terminal nonnegative accepted candidate 12209.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_postPayment_candidate_uniform_upper_bound_finite_cap
import Theorems.Thm_AvramDividend_Classical_local_verification_postPayment_terminal_nonnegative

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_postPayment_candidate_bounded_finite_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (x c : ℝ) (hc : 0 ≤ c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < ENNReal.ofReal c →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ω : Ω) (t : ℝ≥0),
      0 ≤ Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω) ∧
      Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω) ≤ B := by sorry
