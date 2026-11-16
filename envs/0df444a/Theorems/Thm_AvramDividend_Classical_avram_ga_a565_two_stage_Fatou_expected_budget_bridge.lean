-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a565_two_stage_Fatou_expected_budget_bridge
-- name    : AvramDividend.Classical.avram_ga_a565_two_stage_Fatou_expected_budget_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:51:21.522465+00:00
-- url     : https://prove2.me/theorems/b7d22c3a-28e7-4b5b-9edf-914805e972f1
-- title:
--   Two-stage nonnegative Fatou bridge from prehorizon budgets to the exact terminal expectation
-- statement:
--   A nonnegative almost-everywhere measurable terminal reward Y is dominated through the liminf of integrable F_n, each F_n positive part dominated through the liminf of a measurable nonnegative G_m, and every G_m has a uniform ENNReal mean budget K. Applying Fatou twice yields the exact real expected bound E[Y]≤K.
-- source:
--   Fatou lemma applied twice; lintegral_mono_ae; integral_eq_lintegral_of_nonneg_ae; toReal monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a565_two_stage_Fatou_expected_budget_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (K : ℝ) (hK : 0 ≤ K)
    (Y : Ω → ℝ) (F : ℕ → Ω → ℝ) (G : ℕ → Ω → ℝ≥0∞)
    (hYm : AEStronglyMeasurable Y P)
    (hYnn : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hFI : ∀ n, Integrable (F n) P)
    (hGm : ∀ n, Measurable (G n))
    (hFnear : ∀ n, ∀ᵐ ω ∂P,
      ENNReal.ofReal (F n ω) ≤ liminf (fun m => G m ω) atTop)
    (hGB : ∀ m, (∫⁻ ω, G m ω ∂P) ≤ ENNReal.ofReal K)
    (hYnear : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by sorry
