-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_original_finitecap_dividend_and_kink_localtime_fullgrid_nonpositive
-- name    : AvramDividend.Classical.avram_a20_original_finitecap_dividend_and_kink_localtime_fullgrid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:37:09.149604+00:00
-- url     : https://prove2.me/theorems/c98c0fc5-ed99-468c-96e9-317a37f8d010
-- title:
--   Two original finitecap stopped Ito signed physical boundary channels sum nonpositive
-- statement:
--   Under the original finite-cap HJB interior slope and smoothness and nonnegative discounts, the genuine right-dividend caplinear payment correction and upper-cap Gaussian kink local-time correction contribute nonpositive signed finite-grid terms simultaneously. The first is a finite sum of actual dividend amounts D_i and postpayment reserves Y_i, evaluated with caplinear V above the finite cap. The second is the finite Gaussian Tanaka kink correction, with nonnegative local-time L_i and discount K_i. This joins separately Proved exact source bounds 67be5e16 and f4d48799 and forms the two boundary channels of the physical original stopped Gaussian Itô ledger. The true Gaussian spatial/time mesh convergence remains separate.
-- source:
--   Original finitecap physical Ito/Tanaka stopped ledger: genuine caplinear dividend correction and upper cap kink local-time term.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

/-- Original finite-cap right-dividend and Gaussian cap-kink local-time grid channels are jointly nonpositive. -/
theorem AvramDividend.Classical.avram_a20_original_finitecap_dividend_and_kink_localtime_fullgrid_nonpositive
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (S : Finset ℕ) (j : ℕ → ℕ)
    (Y D E L K : ℕ → ℝ)
    (hYlo : ∀ i ∈ S, 0 ≤ Y i)
    (hYhi : ∀ i ∈ S, Y i ≤ C.toReal)
    (hD : ∀ i ∈ S, 0 ≤ D i)
    (hE : ∀ i ∈ S, 0 ≤ E i)
    (hL : ∀ i ∈ S, 0 ≤ L i)
    (hK : ∀ i ∈ S, 0 ≤ K i)
    (hw_cont : ContinuousOn w (Ici 0))
    (hDiff : ∀ i ∈ S, DifferentiableOn ℝ w (Ioo (Y i) C.toReal))
    (hGradBand : ∀ i ∈ S, ∀ t ∈ Ioo (Y i) C.toReal,
      1 ≤ deriv w t) :
    (∑ i ∈ S, E i * (D i + w (Y i) -
        (if Y i + D i ≤ C.toReal then w (Y i + D i)
         else w C.toReal + (Y i + D i - C.toReal)))) +
    (∑ i ∈ S, K i *
      (((1 - deriv w
        (C.toReal * ((((j i + 1 : ℕ) : ℝ) / ((j i + 2 : ℕ) : ℝ))))) / 2) * L i))
    ≤ 0 := by sorry
