-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_jump_laplace_of_product_fubini
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_jump_laplace_of_product_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:19:05.209979+00:00
-- url     : https://prove2.me/theorems/85873471-8964-4045-9f85-12cbff4e7ccc
-- title:
--   Original source primitive integrated Lévy jump generator has exact Laplace image under proved product Fubini
-- statement:
--   For an actual q-scale W of a true spectrally negative Lévy source under Standing and unbounded variation, this theorem identifies the positive-reserve Laplace transform of the *full* integrated compensated generator jump part of U=∫₀ˣW with the original Lévy-Khintchine jump-exponent integral times (ψθ-q)⁻¹/θ, for every positive admissible θ. Crucially the Fubini interchange is justified by the non-circular Proved P2 signed source primitive product L1 (86091fe6) passed to the Proved generic source Fubini theorem 1b6472d7, and its inner x-transform is the exact P2 fixed-jump primitive Laplace identity. The outer ν Bochner integral is not assumed finite by fiat: genuine source quadratic moment supplies it. This is the key analytic missing step toward Laplace[(Γ-q)U]=1/θ and ultimately the non-Gaussian source generator harmonicity.
-- source:
--   Avram Palmowski Pistorius (2007), §3 and Lemma 4 generator computation; source Lévy-Khintchine 933ced80, P2 actual compensated primitive full x×ν product L1, Proved generic Fubini 1b6472d7, and P2 fixed negative-jump transform.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_jump_laplace_of_product_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x y ∂X.ν)) =
      (∫ y in Iio (0 : ℝ),
        Real.exp (θ * y) - 1 -
          θ * (y * (Ioo (-1 : ℝ) 1).indicator
            (fun _ : ℝ => (1 : ℝ)) y) ∂X.ν) *
        ((X.ψ θ - q)⁻¹ / θ) := by sorry
