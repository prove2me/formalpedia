-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja29_original_negative_borel_cell_centred_L2_integrable
-- name    : AvramDividend.Classical.avram_ja29_original_negative_borel_cell_centred_L2_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:43:08.188838+00:00
-- url     : https://prove2.me/theorems/a17f57a3-30a2-4fb8-84b7-74d2bccc09fd
-- title:
--   Original arbitrary negative Borel mark cell has centred L1 and L2 counts
-- statement:
--   On the same original Lévy probability space, any Borel mark cell bounded strictly away from zero has an integrable centred counting variable, zero expectation and integrable square. The exact variance remains a separate Poisson factorial obligation.
-- source:
--   Physical Borel cell component of 67336b2d, the original finite-strip mark-simple certificate feeding ec5fe7b6; reuse Proved original p4_s3 and p4_f3 mean/L2 facts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja29_original_negative_borel_cell_centred_L2_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hSep : B ⊆ Iic (-(1 / ((cut : ℝ) + 1)))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal - r) P ∧
    (∫ ω, (N ω).toReal - r ∂P) = 0 ∧
    Integrable (fun ω => ((N ω).toReal - r) ^ 2) P := by sorry
