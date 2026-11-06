-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_clipped_random_length_positive_lintegral_zero
-- name    : AvramDividend.Classical.avram_p3_2_original_clipped_random_length_positive_lintegral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:21:29.216908+00:00
-- url     : https://prove2.me/theorems/0d9a3257-6b6a-4713-a433-9babce398cc9
-- title:
--   Original BV stopped physical grid nonlinear correction has zero positive outer integral with random length
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, clip every sample-dependent monotone grid time at an arbitrary sample-dependent stopping clock, allowing even the number of clipped cells to vary with the sample. The discounted nonlinear residual correction of the actual original Lévy path and cap-linear test function then has zero positive outer expectation. No unstopped-grid endpoint condition, additional L1 premise, or predictability hypothesis on the sampled grid is assumed.
-- source:
--   Source-exact consequence of public Proved original-X uniform-stopping-grid sign theorem 3c2f33da-f3ab-4a64-9515-4b9915de69b2: every clipped physical grid is monotone and stays below its path-dependent stopping clock.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_caplinear_intrinsic_uniform_stopping_grids
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_clipped_random_length_positive_lintegral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (q : ℝ) (τ : Ω → ℝ≥0) (u : Ω → ℕ → ℝ≥0)
    (hu : ∀ ω, Monotone (u ω))
    (n : Ω → ℕ) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    let G : Ω → ℝ := fun ω =>
      let v : ℕ → ℝ≥0 := fun i => min (u ω i) (τ ω)
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω)
            else 0).toReal
      ∑ i : Fin (n ω),
        Real.exp (-(q * (v i : ℝ))) *
          (V (riskProcess X x D (v i) ω -
            (R (v (i + 1)) - R (v i))) -
           V (riskProcess X x D (v i) ω))
    (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) = 0 := by sorry
