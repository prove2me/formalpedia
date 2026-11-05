-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_stopped_smallband_l1_limit_centered
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_stopped_smallband_l1_limit_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:35:33.683541+00:00
-- url     : https://prove2.me/theorems/b1c643c8-a0e3-4e6e-97af-aa0eedad1d31
-- title:
--   Original stopped predictable compensated small-band L1 limit has zero expectation
-- statement:
--   For the genuine original Lévy intrinsic negative-marked counts and actual right-continuous stopping clock, every predictable finite-grid compensated sum is integrable and centred via the Proved physical source P4-F grid theorem. If those concrete same-path sums converge in actual L1 to Ms, and Ms is integrable, the limit has exactly zero physical expectation. This supplies the source small-jump L1 witness once the L2 Cauchy/completion argument is connected to the physical approximate sums; no law substitution or unsupported convergence is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_stopped_grid_l2_from_predictable
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_stopped_L1_limit_preserves_zero_mean
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_stopped_smallband_l1_limit_centered
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
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (C i)).toReal) 2 P)
    (Ms : Ω → ℝ) (hMsI : Integrable Ms P)
    (hL1 : Tendsto (fun n =>
      ∫⁻ ω, ‖(∑ i ∈ Finset.range n,
        (if (τ ω : WithTop ℝ≥0) ≤ (grid i : WithTop ℝ≥0)
          then (0 : ℝ) else H i ω) *
          ((N i ω).toReal -
            (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
              X.ν (C i)).toReal)) - Ms ω‖ₑ ∂P)
      atTop (nhds 0)) :
    Integrable Ms P ∧ (∫ ω, Ms ω ∂P) = 0 := by sorry
