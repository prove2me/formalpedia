-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:41:04.163783+00:00
-- url     : https://prove2.me/theorems/0439e4ef-b562-4b8f-87cb-b92514a250bd
-- title:
--   Actual original horizon-clipped Lévy jump occupation equals genuine physical predictable intensity on past marked rectangles
-- statement:
--   For the original Lévy source X on exactly Ω/P/rightCont filtration, its intrinsic marked occupation M and actual finite physical predictable intensity N are equal on each adapted marked rectangle wholly inside [0,T], provided precisely P2's outstanding original finite source rate hRate holds. This combines the verified original source-horizon clip, genuine physical clock product mass, source Lévy negative support and σ-finiteness, and exact ENNReal time-length convention. There is no fresh compensator axiom, no alternate jump process, and no finite first-moment assumption. Extending cells across T and from adapted cells to rightCont future is a further deterministic step, with the latter already Proved in P3-B.
-- source:
--   Proved P3-B original stopped source rate, real-to-NNReal physical clock intensity, exact ENNReal length bridge. P2 393b03a8 remains the sole source rate premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_horizon_restricted_source_rate
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_finite_clock_Xnu_marked_cell_rate
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_finite_horizon_marked_rect_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hRate : ∀ (s t : ℝ≥0), s ≤ t →
      ∀ (A : Set Ω), MeasurableSet[𝓕 s] A →
      ∀ (B : Set ℝ), MeasurableSet B →
        M ((Ioc s t ×ˢ A) ×ˢ B) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (M.restrict {p | p.1.1 ≤ T}) ((Ioc s t ×ˢ A) ×ˢ B) =
      N ((Ioc s t ×ˢ A) ×ˢ B) := by sorry
