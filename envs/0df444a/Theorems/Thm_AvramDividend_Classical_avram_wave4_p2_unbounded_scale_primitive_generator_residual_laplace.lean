-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_unbounded_scale_primitive_generator_residual_laplace
-- name    : AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_generator_residual_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:47:37.232622+00:00
-- url     : https://prove2.me/theorems/866d4f77-c0af-4c6d-a75f-9f38df4b618d
-- title:
--   Genuine infinite-variation pure-jump q-scale primitive has exact weighted Lévy generator residual transform
-- statement:
--   For the actual spectrally negative Lévy source under Standing, sigma=0, unbounded variation and a genuine q-scale W with q>0, the source compensated generator of its ordinary primitive U(x)=∫₀ˣW(t)dt is weighted integrable on (0,∞) and the exact Laplace transform of (Γ-q)U equals 1/θ for every positive admissible θ. This is an unconditional source analytic result derived from previously proved global primitive derivative, weighted signed ν×dx Fubini, primitive Laplace transform and the actual Lévy-Khintchine formula. It does not assume generator harmonicity of W or a killed martingale.
-- source:
--   Avram Palmowski Pistorius (2007), §3 and Lemma 4. Exact source generator Def 933ced80; source P2 genuine product L1 86091fe6 and integrated jump Laplace 85873471; positive primitive transform 9f40ea02.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_unbounded_scale_primitive_generator_residual_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
      (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
        q * (∫ t in (0 : ℝ)..x, W t))) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
      (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
        q * (∫ t in (0 : ℝ)..x, W t))) = 1 / θ := by sorry
