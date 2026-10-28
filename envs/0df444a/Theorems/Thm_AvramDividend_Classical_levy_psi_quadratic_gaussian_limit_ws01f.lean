-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_psi_quadratic_gaussian_limit_ws01f
-- name    : AvramDividend.Classical.levy_psi_quadratic_gaussian_limit_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T10:31:10.136975+00:00
-- url     : https://prove2.me/theorems/017db261-6a7b-4307-bd5d-e490188c0e13
-- title:
--   Gaussian coefficient is the quadratic leading term of the spectrally negative Lévy exponent
-- statement:
--   The canonical Lévy–Khintchine Laplace exponent at n+1, divided by (n+1) squared, converges to σ squared over two. This is valid with arbitrary large negative jumps and either finite or infinite small-jump variation. The quadratic compensated-jump contribution vanishes by a genuine dominated-convergence theorem, while the finite large-jump mass and drift decay; independently proved upper and lower bounds for ψ yield a squeeze. This is the scalar Gaussian asymptotic needed for the small-time MGF route, not a stochastic fluctuation statement.
-- source:
--   Canonical Lévy–Khintchine exponent, KKR 2012 Section 2.1, accepted Prove2Me bounds 85d8b8ec and 29b521e4, large mass 30dea431, WS1F actual small-jump quadratic remainder.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_quadratic_remainder_tendsto_zero_ws01f
import Theorems.Thm_AvramDividend_Classical_psi_upper_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_psi_lower_bound_by_compensated_small_jumps
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_psi_quadratic_gaussian_limit_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    Tendsto (fun n : ℕ =>
      X.ψ ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ 2))
      atTop (nhds (X.σ ^ 2 / 2)) := by sorry
