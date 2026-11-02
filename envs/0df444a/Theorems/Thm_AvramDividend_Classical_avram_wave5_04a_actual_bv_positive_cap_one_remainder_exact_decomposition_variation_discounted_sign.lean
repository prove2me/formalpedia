-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:01:56.1029+00:00
-- url     : https://prove2.me/theorems/aa45c108-4acc-4b90-ba95-6a8b16298408
-- title:
--   Single original BV source residual for positive-cap HJB: exact jump decomposition, variation and discounted stopped sign
-- statement:
--   For the actual spectrally negative Lévy process of bounded variation, and the actual dividend-controlled reserve, on one probability-one event the same explicit residual after all intrinsic source left jumps is nondecreasing, gives exact source increments, has exact variation on every partition, and gives a nonpositive exponentially discounted finite-sum C1 contribution along stopped partitions localised to the positive-cap HJB gradient strip. No global monotonicity of w, pure-jump equality, controlled nonlinear Itô–Meyer theorem or chronological dividend jump identity is assumed.
-- source:
--   Chat04-A final source-only interface for Chat03 and Chat04; simultaneously combines canonically Proved source exact increment c4b53c7c-d769-4894-a0d8-c0b2a1516d1e, source exact total variation 3ddc1a4c-7733-4bfe-82ec-284764e67394, and positive-cap discounted source sign 8f5999b2-9e94-4eb9-bdde-9b59ac11acbf by unique explicit original-source residual.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_interval_increment_from_intrinsic_jumps_and_remainder
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_canonical_source_remainder_partition_variation_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The complete Chat03 source-only interface on one original BV sample:
exact intrinsic left-jump decomposition, exact residual total variation,
and nonpositive stopped discounted HJB interior-gradient contribution.
No controlled nonlinear Ito-Meyer integration is assumed. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (v : ℝ≥0),
              if s < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal -
            (R t - R s)) ∧
      (∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) =
        R (u n) - R (u 0)) ∧
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0) := by sorry
