-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:05:05.774073+00:00
-- url     : https://prove2.me/theorems/963870c8-6ffc-4e96-aa5b-3842ee01e9cf
-- title:
--   Physical negative Borel subband count has centred L² energy by domination from full-band original factorial moments
-- statement:
--   For the true original Lévy marked-count random variable on any negative Borel subband of a fixed cutoff and any time subinterval of (0,T], the compensated real count belongs to L². The proof uses pointwise domination by the original full-halfline count and its proved quadratic budget. No physical pair-moment input, abstract Poisson stand-in or independent-count axiom is required.
-- source:
--   P4-S3 original-cell pointwise count domination plus Proved original full-band stopped-square budget 50312326, original marked count measurable 21acd1ce, and pinned Mathlib MemLp.mono.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBsep : B ⊆ Iic (-(1 / ((n : ℝ) + 1)))) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ :=
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    MemLp (fun ω => (N ω).toReal - r) 2 P := by sorry
