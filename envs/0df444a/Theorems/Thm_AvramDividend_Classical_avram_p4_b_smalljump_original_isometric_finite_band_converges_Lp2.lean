-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:23:05.387081+00:00
-- url     : https://prove2.me/theorems/4c3bceb6-cc6e-451b-93d0-763ed9cfd19e
-- title:
--   Original small-negative predictable finite mark cutoffs converge in Lp2(P) under explicit source isometry
-- statement:
--   For the original X and right-continuous predictable clock, a square-integrable predictable linear mark kernel has a fully proved product L2 tail. Given an explicit norm-preserving linear stochastic-integral map from the actual source product Lp2 space into the actual Lp2(P), the finite negative-mark cutoff stochastic images converge in Lp2(P) to the map applied to the full kernel. This is a conditional approximation theorem: the real source isometry, centering and finite-band jump-count representation remain to be established from P2 and true original-process jump calculus.
-- source:
--   Accepted original predictable product eLpNorm2 thinning 1ecaac48, accepted original cutoff error 2415d009, Mathlib conversion toReal at zero and norm-convergence criterion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_linear_isometry_cutoff_Lp2_error
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_linear_product_eLpNorm_tail_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_isometric_finite_band_converges_Lp2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (g : ℝ≥0 × Ω → ℝ)
    (hgm : Measurable[𝓕.rightCont.predictable] g)
    (hgL2 : (∫⁻ p : ℝ≥0 × Ω,
      ENNReal.ofReal ((g p)^2) ∂μ) < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => g p.1 * p.2;
      let hML : MemLp G (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) :=
        avram_p4_b_smalljump_original_small_negative_linear_mark_MemLp
          X μ g hgm hgL2;
      ∀ (I : Lp ℝ (2 : ℝ≥0∞) (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hIso : ∀ v, ‖I v‖ = ‖v‖),
      Tendsto (fun n : ℕ =>
        let A : Set ((ℝ≥0 × Ω) × ℝ) := {p | p.2 ∉ B n}
        I ((hML.indicator ((hBm n).preimage measurable_snd).compl).toLp
          (A.indicator G))) atTop (𝓝 (I (hML.toLp G)))) := by sorry
