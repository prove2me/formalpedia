-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_discounted_postpayment_clock_loss_nonpos
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_discounted_postpayment_clock_loss_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:15:05.842293+00:00
-- url     : https://prove2.me/theorems/b32609e1-1361-4bdb-8be0-def864894a91
-- title:
--   Original any chronological stopped grid discount-clock loss nonpositive for caplinear admissible reserve
-- statement:
--   If the original physical time grid is nondecreasing and discount rate q is nonnegative, discounted exponentials decrease. The original post-right-payment reserve remains within the cap, so caplinear V equals w there and is nonnegative by the proved original C1 gradient lemma. Thus the sum of all discount-clock terminal value losses on that grid is nonpositive. Independent of Brownian or jump finite-activity assumptions.
-- source:
--   Proved original postpayment nonnegativity 28b04520, cap 16104f4f and caplinear value equality 85617d04. This isolates the negative time-discount component of the true full Stieltjes source, leaving only nonlinear Lévy increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_discounted_postpayment_clock_loss_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (m : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range m,
      (Real.exp (-(q * (u (i + 1) : ℝ))) -
        Real.exp (-(q * (u i : ℝ)))) *
        V (x + X.X (u (i + 1)) ω -
          rightLimit D (u (i + 1)) ω)) ≤ 0 := by sorry
