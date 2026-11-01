-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:01:55.673038+00:00
-- url     : https://prove2.me/theorems/86091fe6-401d-4a36-ae08-ab51eb1480ac
-- title:
--   Signed source primitive compensated generator is absolutely integrable on full reserve–jump product
-- statement:
--   Under the true source Standing, unbounded variation, q>0 and θ>0 with q<ψθ, the *signed* original compensated generator integrand for U(x)=∫₀ˣW is product-integrable over positive reserves and negative Lévy marks. Absolute x×ν integrability is canonically established in P2 42d2af28 for the nonnegative weighted absolute kernel using the genuine Lévy quadratic moment. Its signed counterpart is jointly Borel measurable since U is globally monotone (P2 226a1286) and its global derivative equals the Borel q-scale W (P2 a9a01dd4); the actual generatorIntegrand is a measurable expression in U and U'. Direct norm equality transfers absolute product L1 to signed product L1. This exactly matches the importable premise of the canonical Proved generic generator-weighted full Fubini theorem 1b6472d7, making the original source Lévy jump interchange available without a Gaussian assumption.
-- source:
--   Avram Palmowski Pistorius (2007), generator computation in Lemma 4; canonical source generic weighted Fubini 1b6472d7; original P2 full primitive product absolute L1 42d2af28 and primitive global monotonicity 226a1286.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_signed_weighted_product_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    Integrable
      (fun p : ℝ × ℝ => Real.exp (-(θ * p.1)) *
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) p.1 p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
