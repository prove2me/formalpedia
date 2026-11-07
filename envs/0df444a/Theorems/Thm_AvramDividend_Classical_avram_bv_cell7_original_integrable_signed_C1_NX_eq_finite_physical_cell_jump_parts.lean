-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts
-- name    : AvramDividend.Classical.avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:58:25.442767+00:00
-- url     : https://prove2.me/theorems/70ed18c9-ea6f-4e9d-b502-c07ea84ad32e
-- title:
--   Original signed global NX C1 integral equals positive minus negative finite stopped physical cell sums
-- statement:
--   The actual original discounted compact-band C1 real nonlinear jump source, if integrable on the genuine global Lévy jump measure, has a real integral equal to the positive signed-part source on every original stopped physical grid cell minus the negative signed-part source on the same cells. Source-specific discounted and compact-band marks, the ruin/horizon final contact cell, and time-zero exclusion are preserved exactly. The only assumption is the real kernel's genuine Integrable property; the absolute convergence and expected compensated-source work is left to the independent original-process certificates.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_unmasked_global_C1_signed_parts_eq_stopped_physical_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts
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
    let E : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let G : ℝ≥0 × ℝ → ℝ := fun p =>
      c * Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
    let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
    let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((-c) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ E then K p else 0))
    Integrable G NX →
      (∫ p, G p ∂NX) =
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fp (v, Δ v) else 0).toReal -
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fm (v, Δ v) else 0).toReal := by sorry
