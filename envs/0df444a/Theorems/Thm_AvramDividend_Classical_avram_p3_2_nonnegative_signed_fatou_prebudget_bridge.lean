-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
-- name    : AvramDividend.Classical.avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T13:11:11.639964+00:00
-- url     : https://prove2.me/theorems/73aa5a24-9e2f-4a86-b450-599791d3ed50
-- title:
--   Original signed grid expectation bound passes to nonnegative stopped cash-value by Fatou
-- statement:
--   For an integrable nonnegative original stopped cash-plus-terminal random variable Y, a sequence of nonnegative integrable finite meshes F_n with integrable signed error R_n of nonpositive expectation, F_n≤K+R_n a.s., and ENNReal.ofReal Y≤liminf ENNReal.ofReal F_n a.s., conclude E[Y]≤K by Fatou. Provides a second independent integration route from P3-GRID's signed Fatou certificate c1e2f021 to the canonical prebudget.
-- source:
--   Source-faithful measure-theoretic consequence of the original signed Fatou grid certificate c1e2f021. The mesh existence and nonnegativity of the original stopped Y must be independently established. Uses pinned lintegral_liminf_le and ofReal_integral_eq_lintegral_ofReal.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (K : ℝ) (Y : Ω → ℝ)
    (F R : ℕ → Ω → ℝ)
    (hYInt : Integrable Y P)
    (hYNonneg : 0 ≤ᵐ[P] Y)
    (hFMeas : ∀ n, Measurable (F n))
    (hFInt : ∀ n, Integrable (F n) P)
    (hFNonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (R n) P ∧
      (∫ ω, R n ω ∂P) ≤ 0)
    (hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ K + R n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    (∫ ω, Y ω ∂P) ≤ K := by sorry
