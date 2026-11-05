-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_stopped_grid_zero_mean
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_rightcont_stopped_grid_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:47:59.246598+00:00
-- url     : https://prove2.me/theorems/975c069a-269b-45ff-8e8e-e7bf0c047283
-- title:
--   Original right-continuous stopped-grid small-band compensated sum is integrable and mean zero
-- statement:
--   At the actual original right-continuous stopping time τ, the predictable grid mask 1_{τ>grid_i} is measurable at the left endpoint of each original source jump cell. Therefore a stopped-grid weighted sum of intrinsic jump counts has zero expectation by the already proved original right-continuous finite-grid compensation theorem. The square integrability of each masked coefficient and original centred count is still explicitly assumed; no martingale optional sampling, infinite-band limit or Itô–Meyer equation is claimed.
-- source:
--   Public original same-source rightCont lift e58a099d, published first P4-F rightCont finite-grid helper f4fafe37, Mathlib IsStoppingTime measurable-event predicate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_finite_grid_zero_mean
open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_rightcont_stopped_grid_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (C : ℕ → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hBand : ∀ i, C i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (C i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C i))
    (hMeas : ∀ i, Measurable (N i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hMaskedL2 : ∀ i, MemLp (fun ω =>
      if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) then (0 : ℝ) else H i ω) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P)
    (n : ℕ) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range n, (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) then (0 : ℝ) else H i ω) *
        ((N i ω).toReal -
          (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
            X.ν (C i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n, (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0) then (0 : ℝ) else H i ω) *
      ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal)) ∂P) = 0 := by sorry
