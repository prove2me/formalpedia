-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_weighted_jump_product_integrable
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_weighted_jump_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:55:31.106467+00:00
-- url     : https://prove2.me/theorems/42d2af28-8fa2-4087-b1ed-97241899bfea
-- title:
--   Actual unbounded-variation scale primitive has absolutely integrable compensated source Lévy kernel on reserve–jump product
-- statement:
--   For the genuine original spectrally negative Lévy triplet satisfying Standing and unbounded variation, q>0, the actual source scale primitive U(x)=∫₀ˣW has an absolutely weighted product-integrable compensated generator jump kernel for every positive Laplace θ with q<ψθ, over x>0 and negative jumps y<0 against Lebesgue reserve measure times the source Lévy measure. The complete small-jump bound is O(y²) thanks to P2's exact boundary-crossing/interior glued theorem e71795d5; large jumps are uniformly bounded by the true primitive Laplace mass via Proved Chat05a 6e08ca30. The original Lévy condition controls the min(1,y²) envelope; global U'=W supplies joint Borel measurability. It is the missing legitimate absolute Fubini prerequisite for the non-Gaussian primitive Laplace generator calculation, and uses neither generator q-harmonicity nor any martingale identity.
-- source:
--   Avram Palmowski Pistorius (2007), Lemma 4; Kuznetsov Kyprianou Rivero (2013), q-scale Laplace transform; Proved original source Lévy quadratic moment and integrable_prod_of_slice_norm_quadratic_bound, Proved P2 original primitive section bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_weighted_jump_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        |SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) p.1 p.2|)
      ((volume.restrict (Ioi (0 : ℝ))).prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
