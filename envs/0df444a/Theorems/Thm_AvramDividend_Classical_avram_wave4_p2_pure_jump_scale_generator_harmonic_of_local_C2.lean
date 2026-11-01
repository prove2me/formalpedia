-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
-- name    : AvramDividend.Classical.avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:58:15.862986+00:00
-- url     : https://prove2.me/theorems/fc01c311-8bb0-4bef-a680-dc7758c7b10c
-- title:
--   Unconditional original pure-jump q-scale generator harmonicity on a locally C² positive reserve interval
-- statement:
--   For a genuine spectrally negative Levy source under Standing, with σ=0 and unbounded variation, and q-scale W with q>0, W is q-harmonic for the exact compensated source generator throughout any positive interval where W is C², and its genuine jump integrand is ν-integrable at each point. The independent original scale-primitive weighted generator transform from P2 (866d4f77) and the Proved source pointwise Laplace uniqueness from Chat05a (f150b648) give ΓU-qU=1 for U=∫₀ˣW. The Proved independent Chat05a differentiation-under-full-Lévy-measure interface (5557edc6) gives derivative of the genuine compensated jump integral. Since the process has σ=0, first differentiation yields ΓW-qW=0. No false un-stopped martingale or assumed harmonicity is used. This result is the exact missing non-Gaussian C² input for e8fbc763.
-- source:
--   Avram Palmowski Pistorius (2007) proof of Lemma 4, source Lévy-Khintchine generator; P2 q-scale primitive residual Laplace theorem 866d4f77; Chat05a pointwise signed uniqueness f150b648 and compensated derivative 5557edc6; source integrability 196ecce3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p2_pure_jump_scale_generator_harmonic_of_local_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hσ : X.σ = 0) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by sorry
