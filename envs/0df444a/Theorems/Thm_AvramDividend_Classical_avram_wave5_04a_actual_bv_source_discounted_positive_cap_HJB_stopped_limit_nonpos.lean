-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:00:19.965199+00:00
-- url     : https://prove2.me/theorems/a2edb8c9-c132-4f57-b238-e2c21674d0b3
-- title:
--   Original bounded-variation source: discounted positive-cap HJB remainder has a nonpositive stopped real limit
-- statement:
--   For the actual original bounded-variation spectrally negative Levy process, under the same positive-cap HJB local gradient hypothesis as final BV verification, almost surely any real limit of convergent exponentially discounted source residual partition sums is nonpositive if all sampled stopped controlled reserves remain in the strict interior 0<reserve<C. The statement leaves actual convergence and the Itô–Meyer integral identification to Chat03.
-- source:
--   Chat04-A discounted positive-cap source-limit result combining canonically Proved discounted residual sign 8f5999b2-9e94-4eb9-bdde-9b59ac11acbf with le_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_discounted_remainder_nonpos_from_positive_cap_HJB_gradient

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every real limit of stopped, exponentially discounted original BV
source-residual C1 sums is nonpositive while all sampled reserves lie
in the positive-cap HJB gradient region. No Ito-Meyer identification. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_source_discounted_positive_cap_HJB_stopped_limit_nonpos
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
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0)
        (hu : ∀ k : ℕ, Monotone (u k))
        (n : ℕ → ℕ) (hstop : ∀ k : ℕ, u k (n k) ≤ τ ω)
        (hinterior : ∀ k (i : Fin (n k)),
          0 < riskProcess X x D (u k i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u k i) ω) < C)
        (L : ℝ)
        (hlim : Tendsto (fun k : ℕ =>
          ∑ i : Fin (n k),
            -(Real.exp (-(q * (u k i : ℝ))) *
              deriv w (riskProcess X x D (u k i) ω)) *
                (R (u k (i + 1)) - R (u k i))) atTop (𝓝 L)),
        L ≤ 0 := by sorry
