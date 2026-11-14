-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b57_original_gaussian_negative_mark_finite_grid_initial_event_budget
-- name    : AvramDividend.Classical.avram_b57_original_gaussian_negative_mark_finite_grid_initial_event_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:20:48.52526+00:00
-- url     : https://prove2.me/theorems/dd3962aa-41bb-433a-a2d1-b612b3457ca8
-- title:
--   Original finite mixed Gaussian and nonlinear Borel negative-jump physical grid has exact initial-event zero expectation
-- statement:
--   Construct the genuine intrinsic Brownian Gaussian source from the unchanged finite-activity original Lévy process. On any finite collection of physical intervals, add a predictable weighted Gaussian increment and a genuinely marked negative-jump compensated count with a square-integrable predictable weight. For a common event in the original time-zero right-continuous filtration and each physical cell's past, with explicit Gaussian-product integrability, the total real mixed gain is integrable and its expected value on that event is exactly zero. No surrogate noise and no post-ruin continuation.
-- source:
--   B31 original Gaussian existence, JB21 exact initial conditional-centred predictable finite sum, B55 original marked negative Borel physical past-event conditional zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_b55_original_predictable_mark_cell_initial_event_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_jb21_original_initial_condexp_finite_predictable_gain
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b57_original_gaussian_negative_mark_finite_grid_initial_event_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Finset ℕ) (cut : ℕ → ℕ)
    (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (htT : ∀ i ∈ S, t i ≤ T)
    (ε : ℕ → ℝ) (hε : ∀ i ∈ S, 0 < ε i)
    (B : ℕ → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (hBand : ∀ i ∈ S, B i ⊆ Ioo (-1 : ℝ) (-(ε i)))
    (hCut : ∀ i ∈ S, B i ⊆ Iic (-(1 / ((cut i : ℝ) + 1))))
    (HG HJ : ℕ → Ω → ℝ)
    (hHG : ∀ i ∈ S, StronglyMeasurable[𝓕.rightCont (s i)] (HG i))
    (hHJ : ∀ i ∈ S, StronglyMeasurable[𝓕 (s i)] (HJ i))
    (hHJ2 : ∀ i ∈ S, MemLp (HJ i) 2 P)
    (A : Set Ω) (hA0 : MeasurableSet[𝓕.rightCont 0] A)
    (hAJ : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] A) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      ((∀ i ∈ S, Integrable (fun ω =>
        HG i ω * (R (t i) ω - R (s i) ω)) P) →
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
        NX ω (Ioc (s i) (t i) ×ˢ B i)
      let r : ℕ → ℝ := fun i =>
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal
      let F : Ω → ℝ := fun ω =>
        ∑ i ∈ S, (HG i ω * (R (t i) ω - R (s i) ω) +
          HJ i ω * ((N i ω).toReal - r i))
      Integrable F P ∧ (∫ ω in A, F ω ∂P) = 0) := by sorry
