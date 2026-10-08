-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable_nonneg
-- name    : AvramDividend.Classical.bv_exponential_jump_integrable_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:15:37.146734+00:00
-- url     : https://prove2.me/theorems/5a467d54-6e14-43c1-9e5d-ea5d1a194d57
-- title:
--   BV exponential jump integrability for every nonnegative Laplace parameter
-- statement:
--   Extend the already-Proved BV exponential compensator integrability for θ≥1 to every θ≥0. If 0≤θ≤1 and y<0, then e^y≤e^(θy)≤1, hence |e^(θy)-1|≤|e^y-1|. The θ=1 integrability (already Proved) dominates the desired integrand on negative jumps. For θ≥1 reuse the existing theorem unchanged. This closes the actual positive Esscher root φ which can lie strictly below 1.
-- source:
--   Proved bv_exponential_jump_integrable; pinned Mathlib Integrable.mono and monotonicity Real.exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_exponential_jump_integrable_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    IntegrableOn (fun y : ℝ => Real.exp (θ * y) - 1)
      (Iio (0 : ℝ)) X.ν := by sorry
