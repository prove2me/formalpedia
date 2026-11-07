-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensator_H_integrable_NX_eq_finite_physical_C1_signed_cells
-- name    : AvramDividend.Classical.avram_bv_cell7_original_compensator_H_integrable_NX_eq_finite_physical_C1_signed_cells
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:07:18.674194+00:00
-- url     : https://prove2.me/theorems/563caf46-2bcf-4682-ae9e-6172d5570154
-- title:
--   Full original compensated H jump integral as a finite physical-grid signed C1 cell sum
-- statement:
--   For the full source-identical original E/G/H jump kernel used by the accepted compensated HJB theorem, the actual globally marked Lévy NX real H integral equals the difference between two sums of genuine marked jump-time series on the same original ruin/horizon stopped dividend physical cells. The result imports the publicly Proved exact H-to-C1 pointwise identity and original real C1 finite-grid theorem; it requires exactly Integrable(H NX), never a source identity or stochastic hypothesis fabricated for the proof, and includes the single last ruin/horizon contact cell and exclusion of time-zero jumps.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_compensator_H_exact_same_physical_C1_negative_mark_kernel
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_compensator_H_integrable_NX_eq_finite_physical_C1_signed_cells
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q a b : ℝ) (T : ℝ≥0) (m : ℕ) (ω : Ω) :
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b}
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2)
            p.1.1))
      else 0
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0
    let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc a b ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let J : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0)
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
    let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (J p)
    let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0))
    Integrable (fun p => H ((p.1, ω), p.2)) NX →
      (∫ p, H ((p.1, ω), p.2) ∂NX) =
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fp (v, Δ v) else 0).toReal -
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fm (v, Δ v) else 0).toReal := by sorry
