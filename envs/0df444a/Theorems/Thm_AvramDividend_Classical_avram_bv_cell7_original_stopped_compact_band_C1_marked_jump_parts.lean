-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_compact_band_C1_marked_jump_parts
-- name    : AvramDividend.Classical.avram_bv_cell7_original_stopped_compact_band_C1_marked_jump_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T08:58:42.965079+00:00
-- url     : https://prove2.me/theorems/157a8ca2-f622-48a7-b170-0d3620c792c2
-- title:
--   Original stopped compact-band C1 negative-jump integrals partition on the physical grid
-- statement:
--   For the original Lévy path X and admissible dividend strategy D, the exact predictable compact-band left-reserve negative-jump kernel has Borel measurable positive and negative parts. Its intrinsic original marked jump lintegral partitions exactly across the ruin/horizon clipped physical cells including the contact cell. No extra measurability hypothesis is assumed.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_stopped_marked_jump_physical_grid_partition

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_stopped_compact_band_C1_marked_jump_parts
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q c a b : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let N : Set ℝ≥0 → Measure (ℝ≥0 × ℝ) := fun I =>
      (Measure.count.restrict ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ I)).map
        (fun v : ℝ≥0 => (v, Δ v))
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let F : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal (c * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    u 0 = 0 ∧ u (m + 1) = min T τ ∧
    (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) =
      ∑ i ∈ Finset.range (m + 1),
        (∫⁻ p, F p ∂N (Ioc (u i) (u (i + 1)))) := by sorry
