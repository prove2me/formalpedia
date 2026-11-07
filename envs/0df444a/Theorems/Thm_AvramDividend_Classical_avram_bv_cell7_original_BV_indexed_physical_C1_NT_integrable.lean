-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_indexed_physical_C1_NT_integrable
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_physical_C1_NT_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:38:50.940037+00:00
-- url     : https://prove2.me/theorems/c98edc0e-5356-45fb-bbae-88f8a1b206a7
-- title:
--   Every original BV indexed compact C1 source is integrable on one common physical marked-jump sample-path event
-- statement:
--   For any countable sequence of compact positive interior localisation bands of the actual original bounded-variation Lévy process and admissible dividend strategy, one full-measure set of actual sample paths simultaneously supports the integrability of the exact discounted left-reserve negative-mark C1 source with respect to each original intrinsic finite-horizon jump measure at the fixed physical ruin/horizon clock. The proof applies pinned Mathlib ae_all_iff to the separately proved source-specific single-band original BV C1 integrability statement.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_localised_physical_C1_NT_integrable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_indexed_physical_C1_NT_integrable
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
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let Y : ℝ≥0 → ℝ := fun t => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
      let E : Set (ℝ≥0 × ℝ) :=
        {p | p.1 ≤ τ ∧ Y p.1 ∈ Icc (a n) (b n) ∧ p.2 < 0}
      let K : ℝ≥0 × ℝ → ℝ := fun p =>
        if p.1 ≤ T then w (Y p.1 + p.2) - w (Y p.1) else 0
      let G : ℝ≥0 × ℝ → ℝ := fun p =>
        Real.exp (-(q * (p.1 : ℝ))) * (if p ∈ E then K p else 0)
      let Δ : ℝ≥0 → ℝ := fun v =>
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v
      let NT : Measure (ℝ≥0 × ℝ) :=
        ((Measure.count.restrict
          ({v : ℝ≥0 | 0 < v ∧ Δ v ≠ 0} ∩ Ioc 0 T)).map
            (fun v : ℝ≥0 => (v, Δ v)))
      Integrable G NT := by sorry
