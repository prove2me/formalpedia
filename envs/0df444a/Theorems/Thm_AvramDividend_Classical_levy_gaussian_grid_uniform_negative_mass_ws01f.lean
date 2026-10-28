-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_gaussian_grid_uniform_negative_mass_ws01f
-- name    : AvramDividend.Classical.levy_gaussian_grid_uniform_negative_mass_ws01f
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T13:22:39.188123+00:00
-- url     : https://prove2.me/theorems/9697f22d-85aa-4d0a-88cd-1ee9a005f2e0
-- title:
--   Actual Lévy Gaussian shrinking-grid negative slopes have uniform positive probability
-- statement:
--   For an actual spectrally negative Lévy process and Gaussian shrinking grid t_n=1/[m(n+1)]², if the established three-exponential Gaussian moment comparison is strict at m, then the probability that X_{t_n}<C t_n stays uniformly positive for all large n. The proof evaluates three actual Lévy exponential moments, verifies their integrability and measurability, and applies the separately Proved moment-comparison probability lemma. This supplies the nontrivial positive-probability input for the genuine time-zero germ zero-one argument without assuming an unjustified pathwise o(t) jump remainder.
-- source:
--   WS1F actual Lévy grid exponential moment Proved f200dd00 and three-moment negative probability limit Proved 75315fb3; no duplicate under keyword search on 28 October 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_gaussian_grid_exponential_moment_tendsto_ws01f
import Theorems.Thm_AvramDividend_Classical_three_mgf_limits_force_uniform_negative_tail_ws01f

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_gaussian_grid_uniform_negative_mass_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (hm : 0 < m) (C : ℝ)
    (t : ℕ → ℝ≥0)
    (ht : ∀ n : ℕ,
      (t n : ℝ) = 1 / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2))
    (hgap :
      (m : ℝ) ^ 2 *
          (Real.exp ((X.σ ^ 2 / 2) / ((m : ℝ) ^ 2)) - 1) +
        (Real.exp (4 * (X.σ ^ 2 / 2)) - 1) / (m : ℝ) <
          Real.exp (X.σ ^ 2 / 2) - 1) :
    ∃ p : ℝ, 0 < p ∧ ∃ N : ℕ, ∀ n ≥ N,
      p ≤ P.real {ω | X.X (t n) ω < C * (t n : ℝ)} := by sorry
