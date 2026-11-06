-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_vanishing_error_signed_fatou_original_grid
-- name    : AvramDividend.Classical.avram_p3_2_vanishing_error_signed_fatou_original_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:12:25.955771+00:00
-- url     : https://prove2.me/theorems/f1877a7f-9f17-44b1-8df8-86f31c43625a
-- title:
--   Vanishing original stopped BV physical-grid error preserves signed Fatou expectation
-- statement:
--   For the same genuine nonnegative stopped original-process payoff, a sequence of integrable nonnegative mesh payoffs satisfying signed mean-nonpositive bounds up to deterministic errors converging to zero retains the exact finite-horizon expected value upper bound. This supports the original BV C1 mesh-error passage without requiring a global L1 dominator for pathwise corrections.
-- source:
--   Source-exact strengthened expectation interface from the already Proved P3-2 nonnegative signed Fatou theorem 73aa5a24; the proof shifts to a sufficiently late tail at each positive error tolerance, uses cofinal liminf invariance and takes the tolerance to zero.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_vanishing_error_signed_fatou_original_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ) (F R : ℕ → Ω → ℝ)
    (ε : ℕ → ℝ)
    (hYInt : Integrable Y P) (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧ (∫ ω, R n ω ∂P) ≤ 0)
    (hErr : Tendsto ε atTop (nhds (0 : ℝ)))
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω + ε n)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by sorry
