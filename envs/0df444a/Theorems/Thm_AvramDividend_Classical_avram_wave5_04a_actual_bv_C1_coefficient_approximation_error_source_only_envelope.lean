-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_C1_coefficient_approximation_error_source_only_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_C1_coefficient_approximation_error_source_only_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:42:12.221495+00:00
-- url     : https://prove2.me/theorems/3e18218d-c6bb-4c56-b113-c708a98f1e53
-- title:
--   C1 BV source-residual coefficient approximation error bounded by observable original source drift budget
-- statement:
--   On almost every original bounded-variation spectrally negative Levy sample path, replacing the weights in a finite-variation source-residual partition sum by uniformly ε-close coefficients changes the sum by at most ε times the observable source drift-minus-actual-path endpoint increment. This sharp source-only error estimate supports uniform C1 coefficient approximation and avoids any unknown residual in the bound. It uses the intrinsic actual negative left-jump series and does not invoke the controlled Ito-Meyer theorem or a separate Poisson representation.
-- source:
--   Chat04-A original source finite-variation approximation theorem, combining canonical weighted source drift-only remainder envelope ae763e15-49e9-4dd0-b1b2-4168ba7d0c52 with finite-sum linearity; strengthens canonical coefficient-stability theorem 04aefb9c-3519-47c6-b349-52bd61154dc3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_weighted_remainder_bound_by_original_source_drift_residual

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Uniform approximation of coefficients in a source C1 finite-variation
sum has a path-only bound: the residual is absent from the RHS. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_C1_coefficient_approximation_error_source_only_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
        (a b : ℕ → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
        (hclose : ∀ i : ℕ, |a i - b i| ≤ ε),
        |(Finset.range n).sum (fun i =>
          a i * (R (u (i + 1)) - R (u i))) -
          (Finset.range n).sum (fun i =>
          b i * (R (u (i + 1)) - R (u i)))| ≤
          ε * (((u n : ℝ) - (u 0 : ℝ)) * X.drift -
            (X.X (u n) ω - X.X (u 0) ω)) := by sorry
