-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_full_signed_budget_on_paid_nonzero_atoms
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_full_signed_budget_on_paid_nonzero_atoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:42:14.545978+00:00
-- url     : https://prove2.me/theorems/206fe1f7-5fd5-4e83-a563-67942fa7587a
-- title:
--   Original actual paid nonzero Cash atoms satisfy the complete signed right-payment HJB and absolute residual budget
-- statement:
--   Use the exact nonzero paid atoms of the source finite-horizon Cash decomposition as an injectively indexed family of genuine physical NNReal payment times. The already Proved full original source all-eligible right-jump budget then yields summability, nonpositive signed residual and its absolute bound by literal stopped Cash, assuming the honest local secant bound.
-- source:
--   Proved fd02394 original signed right-payment theorem and source paid nonzero clock injection (publication pending).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_paid_nonzero_atom_clocks_injective
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_all_rightjump_budget_no_preruin_premise
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_full_signed_budget_on_paid_nonzero_atoms
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (s : ℝ≥0),
      (s = 0 ∨ (s : ℝ≥0∞) < ruinTime X x D ω) →
        rightLimit D s ω - D s ω ≤
          w (riskProcess X x D s ω) -
          w (riskProcess X x D s ω -
            (rightLimit D s ω - D s ω)))
    (ω : Ω) (T : ℝ≥0) (A : Set ℝ)
    (μatom μdiffuse : Measure ℝ)
    (hsplit : (dividendMeasure D ω).restrict
      (Icc (0 : ℝ) (T : ℝ)) = μatom + μdiffuse)
    (K : ℝ) (hK : 1 ≤ K)
    (hLocalSecant : ∀ a : {t : ℝ | t ∈ A ∧
      t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0},
      w (riskProcess X x D (Real.toNNReal a.1) ω) -
        w (x + X.X (Real.toNNReal a.1) ω -
          rightLimit D (Real.toNNReal a.1) ω) ≤
        K * (rightLimit D (Real.toNNReal a.1) ω -
          D (Real.toNNReal a.1) ω)) :
    let E : Set ℝ := {t | t ∈ A ∧
      t ∈ paymentTimes (ruinTime X x D ω) ∧ μatom {t} ≠ 0}
    let J : E → ℝ := fun a =>
      Real.exp (-(q * (Real.toNNReal a.1 : ℝ))) *
      ((rightLimit D (Real.toNNReal a.1) ω - D (Real.toNNReal a.1) ω) +
        w (x + X.X (Real.toNNReal a.1) ω -
          rightLimit D (Real.toNNReal a.1) ω) -
        w (riskProcess X x D (Real.toNNReal a.1) ω))
    Summable J ∧ (∑' a : E, J a) ≤ 0 ∧
      Summable (fun a : E => |J a|) ∧
      (∑' a : E, |J a|) ≤
        (K - 1) * (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Iic (T : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := by sorry
