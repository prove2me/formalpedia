-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
-- name    : AvramDividend.Classical.avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:54:29.569987+00:00
-- url     : https://prove2.me/theorems/11dd20c2-6975-4a88-bcd2-a6ffef157c38
-- title:
--   Original finite-band bounded predictable jump increments are L² and martingale-centred without separate rate or pair moments
-- statement:
--   For actual original negative Borel marked jumps of a spectrally negative Levy process X on an interval and a bounded predictable square-integrable weight, the centred compensated physical band increment belongs to L² and has conditional expectation zero in the original past filtration. Every count measurability, rate and variance premise is supplied by proved original-process source theorems.
-- source:
--   Proved physical original martingale 662e8550 and original subband centred count L² 963870c8, plus pinned Mathlib HolderTriple L∞×L²→L².

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_original_physical_weighted_finite_band_L2_martingale_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ :=
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    MemLp (fun ω => H ω * ((N ω).toReal - r)) 2 P ∧
    P[(fun ω => H ω * ((N ω).toReal - r)) | 𝓕 s] =ᵐ[P] 0 := by sorry
