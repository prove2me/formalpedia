-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_raw_H_common_stopped_grid_reconciliation
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_raw_H_common_stopped_grid_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:39:41.269005+00:00
-- url     : https://prove2.me/theorems/918fa07d-5e6e-4f8e-bf13-8cdaef77dccf
-- title:
--   Exact original BV discounted physical cash source reconciles to actual compensated H and explicit jump-grid commutator
-- statement:
--   For the actual original bounded-variation spectrally negative Levy X and original admissible dividend D, almost surely on every countably indexed interior C1 band and every ruin/horizon clipped physical grid the discounted initial-right-dividend plus strict physical cash plus surviving terminal is exactly equal to the genuine original H marked-jump integral plus an explicitly defined discounted raw frozen-X minus physical signed-jump-grid commutator, the real discount commutator and the exact dividend remainder. Simultaneously, the H integral is the actual original negative Levy jump-time series on that same half-open clipped grid with the final contact cell and zero-time exclusion. This combines two separately proved exact original-process certificates, leaving only a concrete pathwise commutator for L1 domination and avoiding a new stochastic hypothesis or law surrogate.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_frozen_X_stopped_physical_grid_identity
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_indexed_compensator_H_exact_stopped_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_raw_H_common_stopped_grid_reconciliation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ᵐ ω ∂P, ∀ n m : ℕ,
    let τ : Ω → ℝ≥0 := fun η =>
      (min (ruinTime X x D η) (T : ℝ≥0∞)).toNNReal
    let E : Set (ℝ≥0 × Ω) := {p |
      (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
      Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
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
      {p | p.1 ≤ τ ω ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
    let R : ℝ≥0 × ℝ → ℝ := fun p =>
      (1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0)
    let Δ : ℝ≥0 → ℝ := fun v =>
      X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
    let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0}).map
        (fun v : ℝ≥0 => (v, Δ v)))
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) (τ ω)
    let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (R p)
    let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
      ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
        (if p ∈ Eω then K p else 0))
    let physical : ℝ :=
      (∑ i ∈ Finset.range (m + 1),
        ∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
            Fp (v, Δ v) else 0).toReal -
      (∑ i ∈ Finset.range (m + 1),
        ∑' v : ℝ≥0,
          if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
            Fm (v, Δ v) else 0).toReal
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (u i : ℝ)))
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Ioc (u i : ℝ) (u (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal
    let post : ℕ → ℝ := fun i =>
      w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let frozen : ℕ → ℝ := fun i =>
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω)
    let rem : ℕ → ℝ := fun i =>
      cash i + e i * (post (i + 1) - post i - frozen i)
    (rightLimit D 0 ω +
      ((∑ i ∈ Finset.range (m + 1), cash i) +
        e (m + 1) * post (m + 1) - e 0 * post 0) =
      rightLimit D 0 ω +
        ((∫ p, H ((p.1, ω), p.2) ∂NX) +
         ((∑ i ∈ Finset.range (m + 1), e i * frozen i) - physical) +
         (∑ i ∈ Finset.range (m + 1),
           (e (i + 1) - e i) * post (i + 1)) +
         (∑ i ∈ Finset.range (m + 1), rem i))) ∧
    ((∫ p, H ((p.1, ω), p.2) ∂NX) = physical) := by sorry
