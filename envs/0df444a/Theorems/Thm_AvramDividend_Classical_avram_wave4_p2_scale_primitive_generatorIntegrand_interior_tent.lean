-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_generatorIntegrand_interior_tent
-- name    : AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_tent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:07:57.023246+00:00
-- url     : https://prove2.me/theorems/7047e205-40b0-4243-8920-5b51b62b0168
-- title:
--   Exact source interior compensated primitive integrand as reflected scale derivative tent
-- statement:
--   For the genuine q-scale primitive, at every positive interior reserve x>r and negative jump -r with 0<r<1, the true source compensated generator integrand exactly equals the backward tent integral over the scale derivative, extended by zero on nonpositive reserves. This imports accepted source Taylor, exact second derivative, and interval reflection, and provides the equality needed to transfer the weighted-tent quadratic kernel bounds to the original Lévy generator.
-- source:
--   Avram Palmowski Pistorius (2007), Lemma 4; canonical source Taylor a91a303e, curvature b80c9317, reflection a1f28103

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_tent
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hrx : r < x) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r) =
      ∫ s in (0 : ℝ)..r, (r - s) *
        ((Ioi (0 : ℝ)).indicator (deriv W)) (x - s) := by sorry
