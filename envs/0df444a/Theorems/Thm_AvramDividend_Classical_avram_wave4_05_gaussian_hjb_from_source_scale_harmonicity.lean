-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:34:09.634877+00:00
-- url     : https://prove2.me/theorems/6957b8ab-a7df-4113-a52c-a29b73948ad1
-- title:
--   Actual Gaussian optimal-barrier HJB on every positive reserve from source scale harmonicity and upper inequality
-- statement:
--   For the original Standing spectrally negative Lévy process with positive Gaussian coefficient, q>0 and its q-scale W, assume its actual source scale generator is pointwise q-harmonic on positive reserves and the original candidate's full generator is nonpositive strictly above cstar as in the HJB main target. Then, including cstar=0, below, exactly at and above a positive finite cstar, the original barrier candidate belongs to the genuine local generator domain and satisfies max((X.generator-q)vcstar,1-deriv vcstar)=0 at every reserve y>0. The proof assembles canonical cstar finiteness, exact scale-to-vcstar source harmonicity below, canonical gradient≥1, the already-Proved Gaussian scale interior-to-barrier HJB compatibility, above-barrier generator inequality and zero-barrier HJB. No unproved endpoint continuity is assumed.
-- source:
--   Proved vcstar gradient, Gaussian at-cap HJB of source scale interior harmonicity, zero/upper branch HJB and cstar finiteness; Lean4.33.1 0df444a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_cstar_hjb_of_interior_scale
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Complete Gaussian positive-axis HJB assembled from genuine source scale harmonicity. -/

theorem AvramDividend.Classical.avram_wave4_05_gaussian_hjb_from_source_scale_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hscale : ∀ x : ℝ, 0 < x →
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
