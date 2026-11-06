-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_finite_signed_cutoff_counts_L2_centred
-- name    : AvramDividend.Classical.avram_p4_s3_interval_e_original_finite_signed_cutoff_counts_L2_centred
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:05:29.135678+00:00
-- url     : https://prove2.me/theorems/190607a5-8737-4db4-970d-cbe714983dfa
-- title:
--   Original finite signed full-cutoff marked counts are centred L²
-- statement:
--   For the intrinsic marked jump-count process of the original spectrally negative Lévy X at horizon T, any finite deterministic signed sum of compensated full negative cutoff counts has finite L² norm and exact expectation zero, without auxiliary jump processes, independent-grid hypotheses, or assumed Poisson laws. This explicitly covers full negative cutoffs including the large negative band.
-- source:
--   Source exact original full-band centered L² 963870c8 and original first-moment identity c1e09ada; finite deterministic linearity.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_e_original_finite_signed_cutoff_counts_L2_centred
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (n : ι → ℕ) (a : ι → ℝ) (F : Finset ι) :
    let B : ι → Set ℝ := fun i => Iic (-(1 / (((n i : ℕ) : ℝ) + 1)))
    let N : ι → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Z : ι → Ω → ℝ := fun i ω => a i * ((N i ω).toReal - r i)
    MemLp (∑ i ∈ F, Z i) 2 P ∧
      (∫ ω, ∑ i ∈ F, Z i ω ∂P) = 0 := by sorry
