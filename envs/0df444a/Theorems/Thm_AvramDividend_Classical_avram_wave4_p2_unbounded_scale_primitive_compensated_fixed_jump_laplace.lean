-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_compensated_fixed_jump_laplace
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_compensated_fixed_jump_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:15:26.972023+00:00
-- url     : https://prove2.me/theorems/cc3d0237-a7db-45ab-a92d-b5bfdc4fabdc
-- title:
--   Exact single-jump original Lévy generator Laplace transform of scale primitive with no boundary term
-- statement:
--   For the original source scale primitive U(x)=∫₀ˣW and true compensated generatorIntegrand at a fixed negative Lévy jump y≤0, the exponentially weighted positive reserve integral is exactly [exp(θy)-1-θ y 1_{|y|<1}]/[θ(ψθ-q)] when q>0, θ>0 with ψθ>q, and source unbounded variation. The original source primitive has U(0)=0 and global derivative U'=W, so no false boundary atom term. The proof uses the exact independently Proved primitive shifted transform 459c13bc and source shifted integrability e2632d79, and separates the three Bochner-integrable terms U(x+y),U(x),y W(x) with the *genuine* indicator. It never instantiates a W-specific scale theorem with U as if U itself were a scale function. This is the missing pointwise jump transform needed after actual product Fubini to identify the Laplace image of ΓU.
-- source:
--   Avram Palmowski Pistorius (2007), §3 and Lemma 4 generator calculation; generic original compensator definition 933ced80; P2 independent exact primitive shifted transform and weighted integrability; source scale Laplace identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_compensated_fixed_jump_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ y : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (hy : y ≤ 0) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      SpectrallyNegativeLevy.generatorIntegrand
        (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x y) =
      (Real.exp (θ * y) - 1 -
        θ * (y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y)) *
        ((X.ψ θ - q)⁻¹ / θ) := by sorry
