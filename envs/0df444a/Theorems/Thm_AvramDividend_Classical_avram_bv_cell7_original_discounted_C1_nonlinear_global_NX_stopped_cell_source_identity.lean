-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_discounted_C1_nonlinear_global_NX_stopped_cell_source_identity
-- name    : AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_global_NX_stopped_cell_source_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:30:54.488545+00:00
-- url     : https://prove2.me/theorems/d5f99d08-fa18-4f03-bb83-4db814cee0c0
-- title:
--   Original compact-band discounted C1 nonlinear jump source matches global compensated NX and physical grid
-- statement:
--   For the actual original Lévy and admissible dividend paths, the compact-band pre-right-payment discounted C1 nonlinear negative-jump kernel has measurable positive and negative signed parts. Its integral in the original global Lévy jump measure with the actual ruin/horizon stop indicator is identical to its intrinsic stopped jump measure and exact finite physical-grid jump-time source, preserving zero and the single final contact cell without any unexplained stochastic or measurability assumption.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_admissible_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_finite_clock_negative_mark_value_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_global_NX_stopped_physical_grid_marked_source_identity

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_discounted_C1_nonlinear_global_NX_stopped_cell_source_identity
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
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
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
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        (∫⁻ p, F p ∂N (Ioc (u 0) (u (m + 1)))) ∧
      (∫⁻ p, (if p.1 ∈ Ioc (u 0) (u (m + 1)) then F p else 0) ∂NX) =
        ∑ i ∈ Finset.range (m + 1),
          (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              F (v, Δ v) else 0) := by sorry
