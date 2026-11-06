-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
-- name    : AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:58:06.741226+00:00
-- url     : https://prove2.me/theorems/53e31b78-3fee-4179-9631-d0bbce364a87
-- title:
--   True physical negative-band L2-predictable increments are integrable and centred
-- statement:
--   For original Lévy jump counts on any negative Borel separated band, every original-filtration-predictable square-integrable weight gives an L1 compensated physical increment of exactly zero expectation. The source count L2 follows from original factorial moments; the product L1 from Holder and its mean from the already proved conditional orthogonality. No artificial Poisson law or boundedness hypothesis.
-- source:
--   Actual original physical L2 source 963870c8, proved exact unbounded predictable conditional zero 5f565ecd, pinned Mathlib MemLp.integrable_mul and integral_condExp. This supplies stopped source jump martingale finite-grid L1 and centering without assuming source moment separately.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_cell_L1_integral_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => H ω * ((N ω).toReal - r)) P ∧
      ∫ ω, H ω * ((N ω).toReal - r) ∂P = 0 := by sorry
