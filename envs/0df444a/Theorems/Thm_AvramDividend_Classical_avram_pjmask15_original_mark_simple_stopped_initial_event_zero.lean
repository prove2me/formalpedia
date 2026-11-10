-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pjmask15_original_mark_simple_stopped_initial_event_zero
-- name    : AvramDividend.Classical.avram_pjmask15_original_mark_simple_stopped_initial_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:33:06.38547+00:00
-- url     : https://prove2.me/theorems/7190391d-4dfa-4a47-ae28-2bad821e8a0c
-- title:
--   Original stopped finite-mark compensated grid is centred on an initial event
-- statement:
--   For the actual original Lévy jump-count measure and bounded predictable finite-mark coefficients, masking the coefficients by an initial-filtration event preserves finite-grid conditional centring. Given the standard masked predictable L2 conditions, the compensated stopped finite-mark grid has zero expectation restricted to that event. This is the finite-source initial-event martingale step needed below the pure-jump conditional Itô majorant d8cdab80.
-- source:
--   Derived from Proved 92f30741 by applying its original stopped finite-mark martingale to the same physical coefficients multiplied by the indicator of an initial-filtration event. Source identity and L2 hypotheses are explicit; no auxiliary Lévy process or hypothetical source is introduced.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_finite_mark_family_predictable_L2_mean_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pjmask15_original_mark_simple_stopped_initial_event_zero
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hTime : ∀ i, grid i ≤ T)
    (ε : ℝ) (hε : 0 < ε) (C : ι → ℕ → Set ℝ)
    (hC : ∀ j i, MeasurableSet (C j i))
    (hBand : ∀ j i, C j i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ j i, C j i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (hν : ∀ j i, X.ν (C j i) < ⊤)
    (N : ι → ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ j i, N j i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ C j i))
    (H : ι → ℕ → Ω → ℝ) (A : Set Ω) (hA : MeasurableSet A)
    (hHmask : ∀ j i, StronglyMeasurable[𝓕.rightCont (grid i)]
      (A.indicator (H j i)))
    (hHL2mask : ∀ j i, MemLp (A.indicator (H j i)) 2 P)
    (L : ι → ℝ)
    (hBoundmask : ∀ j i ω, |A.indicator (H j i) ω| ≤ L j)
    (n : ℕ) (F : Finset ι) :
    (∫ ω in A, ∑ j ∈ F, ∑ i ∈ Finset.range n,
      (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
        then (0 : ℝ) else H j i ω) *
      ((N j i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C j i)).toReal) ∂P) = 0 := by sorry
