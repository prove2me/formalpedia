-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_gaussian_grid_exponential_moment_tendsto_ws01f
-- name    : AvramDividend.Classical.levy_gaussian_grid_exponential_moment_tendsto_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:11:21.049327+00:00
-- url     : https://prove2.me/theorems/f200dd00-1e9a-4f0e-9412-96fbba17ed1b
-- title:
--   Actual Lévy exponential moments converge on each Gaussian shrinking grid
-- statement:
--   For an actual spectrally negative Lévy process and every reciprocal-square shrinking time grid t_n=1/[m(n+1)]², the expectation of the shifted exponential at positive integer Laplace parameter k(n+1) converges to exp((σ²/2)(k/m)²). This is a genuine use of the supplied Lévy process law, not merely analytic manipulation of ψ: the proof applies the Proved exponential-eigenfunction integral identity and the new actual Gaussian quadratic ψ limit, with exact algebra for the finite linear boundary shift. It applies without Standing or bounded-variation restrictions and is the common stochastic input for all three Gaussian moment scales.
-- source:
--   Canonical actual Lévy transition exponential eigenfunction ee03658e, remotely Proved Gaussian exponent limit 017db261 and analytic shrinking-grid limit 53cc4829; WS1F zero-barrier Gaussian branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_quadratic_gaussian_limit_ws01f
import Theorems.Thm_AvramDividend_Classical_quadratic_exponent_gaussian_grid_mgf_limit_ws01f
import Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_eigenfunction

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_gaussian_grid_exponential_moment_tendsto_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m k : ℕ) (hm : 0 < m) (hk : 0 < k) (C : ℝ)
    (t : ℕ → ℝ≥0)
    (ht : ∀ n : ℕ,
      (t n : ℝ) = 1 / (((m : ℝ) * ((n : ℝ) + 1)) ^ 2)) :
    Tendsto (fun n : ℕ =>
      ∫ ω, Real.exp
        (((k : ℝ) * ((n : ℝ) + 1)) *
          (X.X (t n) ω - C * (t n : ℝ))) ∂P)
      atTop (nhds
        (Real.exp ((X.σ ^ 2 / 2) * ((k : ℝ) / (m : ℝ)) ^ 2))) := by sorry
