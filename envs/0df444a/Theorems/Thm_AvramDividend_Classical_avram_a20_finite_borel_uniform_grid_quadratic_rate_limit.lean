-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_finite_borel_uniform_grid_quadratic_rate_limit
-- name    : AvramDividend.Classical.avram_a20_finite_borel_uniform_grid_quadratic_rate_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:47:44.64533+00:00
-- url     : https://prove2.me/theorems/f3ec9004-1014-4571-993d-e2e03a724164
-- title:
--   Uniform chronological pair-grid quadratic rate tends to half the squared arbitrary finite Borel intensity
-- statement:
--   For an arbitrary real mark measure μ with finite mass on B and nonnegative physical horizon T, the extended-nonnegative finite-grid chronological expected pair-rate expression n(n−1)/2 × (T μ(B)/n)² converges to (T μ(B))²/2. Reuse the already Proved universal real triangular mesh limit, lift through continuous ENNReal.ofReal, and identify the finite Borel rate conversion through the separately verified quadratic rate identity. This is the analytic rate limit needed for the original arbitrary-Borel Lévy jump factorial expectation and avoids relying on any cutoff-specific source.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_finite_borel_uniform_grid_quadratic_rate_limit
    (μ : Measure ℝ) (B : Set ℝ)
    (T : ℝ≥0) (hν : μ B < ⊤) :
    Tendsto
      (fun m : ℕ => ENNReal.ofReal
        (((m : ℝ) * ((m : ℝ) - 1) / 2) *
          (((T : ℝ) * (μ B).toReal) ^ 2 / (m : ℝ) ^ 2)))
      atTop (𝓝 ((((T : ℝ≥0∞) * μ B) ^ 2) / 2)) := by sorry
