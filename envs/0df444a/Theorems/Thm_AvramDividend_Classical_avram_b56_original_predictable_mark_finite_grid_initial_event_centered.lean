-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b56_original_predictable_mark_finite_grid_initial_event_centered
-- name    : AvramDividend.Classical.avram_b56_original_predictable_mark_finite_grid_initial_event_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:18:42.461513+00:00
-- url     : https://prove2.me/theorems/ea6c94f2-aa6c-4c1a-9876-b6377a87a1f3
-- title:
--   True original finite-grid predictable negative marked compensated jump gain is centred on a common past event
-- statement:
--   For finitely many physical original negative Borel mark cells with square-integrable original-past predictable weights, a common event measurable in each physical past filtration has zero expected compensated jump gain after summing all cells, with an integrable gain. No surrogate noise or global jump-square moment.
-- source:
--   Proved original physical predictable mark eventwise conditional centring B55 and restricted integrability of finite sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b55_original_predictable_mark_cell_initial_event_mean_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b56_original_predictable_mark_finite_grid_initial_event_centered
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (S : Finset ι) (cut : ι → ℕ)
    (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (htT : ∀ i ∈ S, t i ≤ T)
    (ε : ι → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-(ε i)))
    (hCut : ∀ i ∈ S,
      B i ⊆ Iic (-(1 / ((cut i : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (H i))
    (hHL2 : ∀ i ∈ S, MemLp (H i) 2 P)
    (A : Set Ω)
    (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] A) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let N : ι → Ω → ℝ≥0∞ := fun i ω =>
      NX ω (Ioc (s i) (t i) ×ˢ B i)
    let r : ι → ℝ := fun i =>
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ S, H i ω * ((N i ω).toReal - r i)
    Integrable F P ∧ (∫ ω in A, F ω ∂P) = 0 := by sorry
