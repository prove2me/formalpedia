-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_jump_only_H_physical_reconciliation
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_C1_jump_only_H_physical_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:17:21.197572+00:00
-- url     : https://prove2.me/theorems/99abda83-abf1-4f5e-b079-97e84f782b28
-- title:
--   Exact original BV discounted C1 grid source with drift and physical H separated and jump-only discrepancy exposed
-- statement:
--   For the original bounded-variation spectrally negative Levy X, original admissible dividend D and each stopped ruin/horizon physical grid, the exact discounted C1 cash and surviving terminal identity is decomposed into the original derivative-weighted continuous BV drift, actual signed original H jump integral, the explicitly defined aggregate-negative-jump value change minus the genuine physical signed H jump-cell sum, original C1 cross and Taylor terms, discount commutator and dividend remainder. The independent original H-to-physical equality holds on the same full-measure event for all compact interior bands and mesh sizes. This is a source-exact, non-stochastic algebraic reconciliation using previously Proved d51199a8 and 43fc8e19, retaining time-zero right dividend, zero-jump exclusion and final contact. Unlike the full frozen-X-minus-H difference, the isolated jump-only commutator does not accidentally contain the nonvanishing continuous BV drift. Its actual L1 vanishing remains a separate theorem obligation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_discounted_C1_six_term_stopped_physical_grid_identity
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_indexed_compensator_H_exact_stopped_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_discounted_C1_jump_only_H_physical_reconciliation
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
    let Ypre : ℝ≥0 → ℝ := fun t => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let Eω : Set (ℝ≥0 × ℝ) :=
      {p | p.1 ≤ τ ω ∧ Ypre p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
    let K : ℝ≥0 × ℝ → ℝ := fun p =>
      if p.1 ≤ T then w (Ypre p.1 + p.2) - w (Ypre p.1) else 0
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
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
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
        ((∑ i ∈ Finset.range (m + 1),
           e i * (deriv w (z i) * c i)) +
         (∫ p, H ((p.1, ω), p.2) ∂NX) +
         ((∑ i ∈ Finset.range (m + 1),
             e i * (w (z i - j i) - w (z i))) - physical) +
         (∑ i ∈ Finset.range (m + 1),
           e i * (w (z i + c i - j i) - w (z i + c i) -
             w (z i - j i) + w (z i))) +
         (∑ i ∈ Finset.range (m + 1),
           e i * (w (z i + c i) - w (z i) - deriv w (z i) * c i)) +
         (∑ i ∈ Finset.range (m + 1),
           (e (i + 1) - e i) * post (i + 1)) +
         (∑ i ∈ Finset.range (m + 1), rem i))) ∧
    ((∫ p, H ((p.1, ω), p.2) ∂NX) = physical) := by sorry
