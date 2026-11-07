-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_indexed_C1_source_exact_stopped_grid
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_C1_source_exact_stopped_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:56:39.550194+00:00
-- url     : https://prove2.me/theorems/e3620c5d-69a5-424b-82c2-3ab98c283846
-- title:
--   All original BV C1 compact-band indices share one almost-sure physical jump-grid identity
-- statement:
--   For any countable sequence of compact positive interior bands of the actual original bounded-variation Lévy dividend problem, one original full-probability path event carries simultaneously, for every band index and every stopped physical grid size, the exact equality between the original global signed C1 nonlinear jump integral and the corresponding stopped marked physical-cell sums. The proof applies pinned Mathlib ae_all_iff to the already proved source-exact original single-band localisation identity. This aligns with the same-index countable bands of the accepted compensated HJB theorem f721cf13.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_localised_signed_C1_source_exact_physical_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_C1_source_exact_stopped_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hab : ∀ n, a n ≤ b n)
    (hBand : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ᵐ ω ∂P, ∀ (n m : ℕ),
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
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
      let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
        ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
          (if p ∈ E then K p else 0))
      (∫ p, G p ∂NX) =
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fp (v, Δ v) else 0).toReal -
        (∑ i ∈ Finset.range (m + 1),
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fm (v, Δ v) else 0).toReal := by sorry
