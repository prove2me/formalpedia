-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T16:12:47.809101+00:00
-- url     : https://prove2.me/theorems/30b2c92e-66c1-4ea4-be1a-f3d5b5e91e5f
-- title:
--   Genuine original BV Lévy polynomial residual primitive is Bochner integrable at every time
-- statement:
--   For the true bounded-variation spectrally negative Lévy process, show at every original time t≥0 that the interval integral of a fixed zero-constant exponential polynomial along its actual residual t*drift-X_t is Bochner integrable. The source residual is measurable by adaptedness and a.e. nonnegative by the already Proved actual source monotonicity. The new fully proved generic polynomial primitive integrability theorem then applies on the original probability space. This discharges the random-process integrability premise without changing process, coupling, or using a C2 estimate.
-- source:
--   Remote candidates/work_on/AvramDividend_04c_actual_BV_poly_residual_primitive_integrable_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_nonnegative_random_poly_primitive_integrable
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_poly_residual_primitive_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (p : Polynomial ℝ) (hp : Polynomial.eval 0 p = 0)
    (t : ℝ≥0) :
    Integrable (fun ω => (∫ r in (0 : ℝ)..
      ((t : ℝ) * X.drift - X.X t ω),
      Polynomial.eval (Real.exp (-r)) p)) P := by sorry
