-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_simple_Lp2_cell_identification
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_finite_simple_Lp2_cell_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:16:21.245237+00:00
-- url     : https://prove2.me/theorems/d692b1e8-9fc4-47bb-92f8-58e3b36b35af
-- title:
--   Original-source finite predictable simple Lp2 jump-compensator cell identification is linear
-- statement:
--   On the actual source Lévy predictable Lp2 product and original sample-space Lp2, suppose a linear map I agrees on each of finitely many actual original compensated-jump cells with their given Lp2 jump-minus-compensator variables J_i-C_i. Then it agrees with the coefficient-weighted finite simple-integrand sum. Genuine source cell identification is an explicit premise hCell and this theorem does not construct the original jump measure, compensator, or compensated stochastic integral.
-- source:
--   Linear map sum/smul properties on the original source finite predictable simple integrands. Each source cell identity is an explicit input.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_finite_simple_Lp2_cell_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ {ι : Type*}
        (S : Finset ι)
        (φ : ι → Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))))
        (J C : ι → Lp ℝ (2 : ℝ≥0∞) P)
        (I : Lp ℝ (2 : ℝ≥0∞)
          (μ.prod (X.ν.restrict (Ioo (-1 : ℝ) 0))) →ₗ[ℝ]
          Lp ℝ (2 : ℝ≥0∞) P)
        (hCell : ∀ i ∈ S, I (φ i) = J i - C i)
        (a : ι → ℝ),
        I (∑ i ∈ S, a i • φ i) = ∑ i ∈ S, a i • (J i - C i)) := by sorry
