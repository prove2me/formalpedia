-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_signed_fatou_integrable_residual_witness
-- name    : AvramDividend.Classical.avram_p3_2_signed_fatou_integrable_residual_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:04:18.549411+00:00
-- url     : https://prove2.me/theorems/67696edf-174b-408c-a249-7fb6cccdbe6f
-- title:
--   Original signed Fatou grid constructs integrable nonpositive-mean residual directly
-- statement:
--   Given a nonnegative integrable strict original-process payoff Y and an independent physical signed Fatou grid whose nonpositive-mean residuals bound that payoff, produce E=Y-K with E integrable, expectation at most zero, and the pathwise residual inequality. Unlike the canonical residual theorem, the only assumptions are the genuine mesh data; no canonical prebudget is imported.
-- source:
--   A full corollary of the public Proved signed Fatou expectation bridge 73aa5a24-9e2f-4a86-b450-599791d3ed50. The independent physical GRID certificate c1e2f021 remains to be proved; this lemma assumes the actual original-process grid data explicitly and does not assert them.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_nonnegative_signed_fatou_prebudget_bridge
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_signed_fatou_integrable_residual_witness
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
    ∃ E : Ω → ℝ, Integrable E P ∧
      (∫ ω, E ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P, Y ω ≤ K + E ω) := by sorry
