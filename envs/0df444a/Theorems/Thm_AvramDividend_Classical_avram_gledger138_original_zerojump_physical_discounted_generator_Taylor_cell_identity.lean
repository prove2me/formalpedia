-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger138_original_zerojump_physical_discounted_generator_Taylor_cell_identity
-- name    : AvramDividend.Classical.avram_gledger138_original_zerojump_physical_discounted_generator_Taylor_cell_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:04:35.466611+00:00
-- url     : https://prove2.me/theorems/b4701dcb-6a20-4c65-94a7-50cc15b5ecd6
-- title:
--   Exact original zero-jump Gaussian physical cell Taylor and discount generator remainder
-- statement:
--   At original source times s and t, the exact discounted physical reserve-value difference minus the original compensated Gaussian linear/quadratic increment and zero-jump HJB generator drift splits into four terms: discount Euler error, discount/space cross error, local C2 Taylor remainder, and a physical drift cross/quadratic error. The source process is the same X, the coefficient is x+X.X s-rightLimit D s, and no auxiliary Brownian source is introduced.
-- source:
--   Specialisation of Proved gledger79 original Gaussian algebraic cell identity with Proved p4F11 zero-jump generator split, using the actual physical postpayment source of Open gledger50 Taylor L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger138_original_zerojump_physical_discounted_generator_Taylor_cell_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (s t : ℝ≥0) :
    let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
    let E : ℝ := Real.exp (-(q * (s : ℝ)))
    let F : ℝ := Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let Z : ℝ := x + X.X t ω - rightLimit D s ω
    let z : ℝ := X.X t ω - X.X s ω - δ * X.c
    ((F - E) * w y + F * (w Z - w y)) -
      E * (deriv w y * z + (iteratedDeriv 2 w y / 2) * (z ^ 2 - δ * X.σ ^ 2)) -
      δ * E * (X.generator w y - q * w y) =
    (F - E + q * δ * E) * w y +
      (F - E) * (w Z - w y) +
      E * (w Z - w y - deriv w y * (z + X.c * δ) -
        (iteratedDeriv 2 w y / 2) * (z + X.c * δ) ^ 2) +
      E * iteratedDeriv 2 w y * (X.c * δ * z + X.c ^ 2 * δ ^ 2 / 2) := by sorry
