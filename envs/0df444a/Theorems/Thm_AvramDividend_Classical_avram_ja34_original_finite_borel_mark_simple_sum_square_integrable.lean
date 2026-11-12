-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
-- name    : AvramDividend.Classical.avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:18:41.017386+00:00
-- url     : https://prove2.me/theorems/f2adc78c-5470-423f-b8ca-5d8080633316
-- title:
--   Physical finite Borel mark-simple compensated sums have integrable squares
-- statement:
--   Every fixed finite real deterministic linear combination of compensated original-path negative Borel marked-jump counts has a square-integrable value under original P, when marks are separated from zero. This is one necessary original finite mark-simple L2 certificate for JA28 and does not assume or assert the missing exact spatial-mark Poisson isometry.
-- source:
--   Original physical JA28 67336b2d finite Borel mark-simple prerequisites. Proved JA29 and JA31 with Mathlib memLp_finset_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja29_original_negative_borel_cell_centred_L2_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_borel_mark_count_filtration_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja34_original_finite_borel_mark_simple_sum_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) (cut : ℕ)
    (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hSep : ∀ i ∈ Finset.range K,
      B i ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          (((t : ℝ≥0∞) * X.ν (B i)).toReal))
    Integrable (fun ω => (F ω) ^ 2) P := by sorry
