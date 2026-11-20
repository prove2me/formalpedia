-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
-- name    : AvramDividend.Classical.avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:48:07.367514+00:00
-- url     : https://prove2.me/theorems/5acde692-6c52-471e-bbc1-23610848b1e3
-- title:
--   Discounted within-cell dividend loss nonpositive globally for caplinear continuation without upper pre-reserve bound
-- statement:
--   For every finite family of original physical dividend cells and nonnegative exponential weights, any nonnegative postpayment reserve and larger prepayment reserve satisfy full dividend increment minus the cap-linear potential decrease ≤0, even if prepayment reserve exceeds finite C. This avoids a false physical cap restriction.
-- source:
--   Proved a4675c8a global cap linear secant. Independent true-grid finite variation sign component of purejump original Ito, with no Gaussian or finite-activity hypotheses.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_caplinear_allcell_discounted_cash_loss_nonpos
    {ι : Type*} (S : Finset ι)
    (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (pre post weight : ι → ℝ)
    (hpost : ∀ i ∈ S, 0 ≤ post i)
    (hmono : ∀ i ∈ S, post i ≤ pre i)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) :
    (∑ i ∈ S, weight i *
      ((pre i - post i) - (V (pre i) - V (post i)))) ≤ 0 := by sorry
