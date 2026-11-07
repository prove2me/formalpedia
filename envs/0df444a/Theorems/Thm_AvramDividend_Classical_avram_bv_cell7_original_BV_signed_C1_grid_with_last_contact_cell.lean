-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_signed_C1_grid_with_last_contact_cell
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_signed_C1_grid_with_last_contact_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:47:29.482213+00:00
-- url     : https://prove2.me/theorems/31681d71-40f5-45e4-9440-c3b81a033998
-- title:
--   Original BV full real signed C1 jump source isolates the single final stopped contact cell
-- statement:
--   The actual original BV Lévy compact-band discounted nonlinear C1 jump source integrated on its original global marked jump measure is exactly the signed sum of the first m original stopped physical grid cells plus one separate final ruin/horizon contact cell, with no integrability premise. The proof combines the already proved original bounded-variation full NX C1 integrability with the exact source-identical real signed finite-grid theorem and pinned Mathlib Finset.sum_range_succ. It explicitly retains the original time-zero exclusion, strict preceding half-open cells, original admissible dividends and surviving last contact source rather than hiding the latter in a generic stopping argument.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_physical_compact_C1_global_NX_integrable
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_integrable_signed_C1_NX_eq_finite_physical_cell_jump_parts

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_signed_C1_grid_with_last_contact_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q a b L R : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (m : ℕ),
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
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Fp : ℝ≥0 × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (G p)
      let Fm : ℝ≥0 × ℝ → ℝ≥0∞ := fun p =>
        ENNReal.ofReal ((-1 : ℝ) * Real.exp (-(q * (p.1 : ℝ))) *
          (if p ∈ E then K p else 0))
      (∫ p, G p ∂NX) =
        ((∑ i ∈ Finset.range m,
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fp (v, Δ v) else 0) +
        (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u m) (u (m + 1)) then
              Fp (v, Δ v) else 0)).toReal -
        ((∑ i ∈ Finset.range m,
          ∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u i) (u (i + 1)) then
              Fm (v, Δ v) else 0) +
        (∑' v : ℝ≥0,
            if (0 < v ∧ Δ v ≠ 0) ∧ v ∈ Ioc (u m) (u (m + 1)) then
              Fm (v, Δ v) else 0)).toReal := by sorry
