-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_canonical_isometric_finite_band_converges_Lp2
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_isometric_finite_band_converges_Lp2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:14:36.181956+00:00
-- url     : https://prove2.me/theorems/5cde222d-0f41-42a2-8e76-4b9360a09825
-- title:
--   Original small-negative canonical near-zero band cutoffs converge in L2 under source isometry
-- statement:
--   For the actual source spectrally negative Lévy process and predictable quadratic-integrable original coefficient, the images of finite-band approximants with canonical small marks (-1/(n+1),0) removed converge in Lp2 of the original probability P under an explicitly assumed norm-preserving linear map. This is the direct canonical specialisation of already Proved source energy-thinning and conditional isometric convergence lemmas; it does not construct the stochastic jump integral or claim compensation has been established.
-- source:
--   Accepted original source isometric finite-band convergence 4c3bceb6 and canonical band antitone-empty theorem 7de0c448.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_canonical_negative_mark_bands_antitone_empty
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_canonical_isometric_finite_band_converges_Lp2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => g p.1 * p.2;
      let hML : MemLp G (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) :=
        avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
          X μ g hgm hgL2;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      Tendsto (fun n : ℕ =>
        let A : Set ((ℝ≥0 × Ω) × ℝ) :=
          {p | p.2 ∉ Ioo (-(1 : ℝ) / ((n + 1 : ℕ) : ℝ)) 0}
        I ((hML.indicator (measurableSet_Ioo.preimage measurable_snd).compl).toLp
          (A.indicator G))) atTop (𝓝 (I (hML.toLp G)))) := by sorry
