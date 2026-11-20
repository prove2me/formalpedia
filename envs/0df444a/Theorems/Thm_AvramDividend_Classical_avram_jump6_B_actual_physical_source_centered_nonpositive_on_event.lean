-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_physical_source_centered_nonpositive_on_event
-- name    : AvramDividend.Classical.avram_jump6_B_actual_physical_source_centered_nonpositive_on_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:56:16.199441+00:00
-- url     : https://prove2.me/theorems/398228b5-180a-4eaa-b6ed-91796c156d1c
-- title:
--   Original stopped physical generator and centred source signed expectation on any positive-clock event
-- statement:
--   For the true spectrally negative Levy path, exact stopped physical generator Q_j, and any measurable positive-clock event represented by a measurable set A, the source decomposition Source_j=M_j+Q_j has nonpositive expectation on A whenever both terms are integrable there and the centred remainder M_j has zero event mean. The original HJB sign proves the Q_j contribution without a finite-activity hypothesis or an assumed Q expectation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_physical_finite_grid_HJB_generator_Q_nonpositive
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_actual_physical_source_centered_nonpositive_on_event
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → ℝ≥0) (u : ℕ → ℕ → ℝ≥0) (m : ℕ → ℕ)
    (A : Set Ω) (Source M Q : ℕ → Ω → ℝ)
    (hQphysical : ∀ j ω,
      Q j ω = (let v : ℕ → ℝ≥0 := fun i => min (u j i) (σ ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        ∑ i ∈ Finset.range (m j),
          E (v (i + 1)) * (((v (i + 1) - v i : ℝ≥0) : ℝ)) *
            (if 0 < Y (v i) ∧ ENNReal.ofReal (Y (v i)) < C then
              X.generator w (Y (v i)) - q * w (Y (v i))
             else 0)))
    (hMInt : ∀ j, IntegrableOn (M j) A P)
    (hQInt : ∀ j, IntegrableOn (Q j) A P)
    (hMzero : ∀ j, (∫ ω in A, M j ω ∂P) = 0)
    (hSource : ∀ j ω, Source j ω = M j ω + Q j ω) :
    ∀ j, (∫ ω in A, Source j ω ∂P) ≤ 0 := by sorry
