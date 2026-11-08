-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_levy_square_lintegral_finite
-- name    : AvramDividend.Classical.avram_gen15_singular_density_levy_square_lintegral_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:24:38.276251+00:00
-- url     : https://prove2.me/theorems/253010fc-1955-491a-98db-b8a369606060
-- title:
--   Singular negative jump measure satisfies the original Levy measure square-moment field
-- statement:
--   The proposed singular negative Levy measure satisfies the exact extended nonnegative square-jump integral finiteness field required by SpectrallyNegativeLevy.nu_integrable. It follows from the previously proved exact real square-jump moment two-thirds using genuine Bochner integrability and monotonicity of nonnegative integration.
-- source:
--   Accepted square-jump moment and pinned integral_undef, ofReal_integral_eq_lintegral_ofReal, lintegral_mono and ENNReal.ofReal_le_ofReal.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen15_singular_density_levy_square_lintegral_finite :
    (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) < ⊤ := by sorry
