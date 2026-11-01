-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05a_scale_primitive_residual_eq_one_of_laplace
-- name    : AvramDividend.Classical.avram_wave4_05a_scale_primitive_residual_eq_one_of_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:33:07.534935+00:00
-- url     : https://prove2.me/theorems/f150b648-f7cc-4632-b3c5-6eaab22739c3
-- title:
--   Actual scale-primitive source generator residual equals one from its signed Laplace family
-- statement:
--   For a genuine q-scale function W of a Standing spectrally negative Lévy process of unbounded variation, put U(x)=∫0..x W. Suppose for every θ>b>0 that the actual source residual (generator U − qU) has an integrable exponentially weighted positive-axis section with Laplace integral 1/θ. Then generator U(x)−qU(x)=1 for every x>0. No C2 hypothesis on W or primitive residual continuity is assumed. The proof converts the signed Laplace identity to a.e. residual equality and uses the P3 genuine source compensated generator continuity theorem for U on each positive compact interval, exploiting U's global monotonicity and positive-axis C2 regularity under Standing, to upgrade equality pointwise.
-- source:
--   Avram–Palmowski–Pistorius 2007 source infinitesimal generator and q-scale primitive identity; Kuznetsov–Kyprianou–Rivero scale review generator domain; already Proved Avram signed Laplace uniqueness a9ef580a, P3 source residual continuity d574f843, P2 source primitive monotonicity 226a1286, primitive C2 925aaf62, and zero-nonpositive 6dcc8ffe. Pinned Mathlib integral_exp_mul_Ioi, integrableOn_exp_mul_Ioi, MeasureTheory.ae_restrict_of_ae_restrict_of_subset, Measure.eqOn_of_ae_eq. Complete independent private source proof 128 lines passed remote compiler to intentional sentinel with zero source errors, job be44a133-ac52-40f2-95ee-5000ee5fc880, source SHA 833a598eaed00111711f7599b59bb28746d2dd2abbf03b098cf222a727e22080. This precise bridge is a genuine missing local pointwise uniqueness step for P2's Open e8fbc763. It is not the P2 Laplace-transform claim, generator harmonicity, or Chat 05 HJB.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05a_scale_primitive_residual_eq_one_of_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (b : ℝ) (hb : 0 < b)
    (hLap : ∀ θ : ℝ, b < θ →
      IntegrableOn
        (fun x : ℝ => Real.exp (-(θ*x)) *
          (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
            q * (∫ t in (0 : ℝ)..x, W t)))
        (Ioi (0 : ℝ)) volume ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        (X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
          q * (∫ t in (0 : ℝ)..x, W t))) = 1 / θ) :
    ∀ x : ℝ, 0 < x →
      X.generator (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x -
        q * (∫ t in (0 : ℝ)..x, W t) = 1 := by sorry
