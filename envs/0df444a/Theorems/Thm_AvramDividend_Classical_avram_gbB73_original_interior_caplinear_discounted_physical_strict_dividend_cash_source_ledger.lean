-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB73_original_interior_caplinear_discounted_physical_strict_dividend_cash_source_ledger
-- name    : AvramDividend.Classical.avram_gbB73_original_interior_caplinear_discounted_physical_strict_dividend_cash_source_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:24:53.651531+00:00
-- url     : https://prove2.me/theorems/ebb58968-6dde-4c12-914b-f54d5a7f8a07
-- title:
--   Original finite-cap physical-grid discounted prepayment spatial source bounds true strict dividend cash and terminal caplinear postpayment value
-- statement:
--   For the original Lévy source and actual admissible dividend strategy, at any interior clipped cap c and every finite physical Gaussian mesh with genuine pre-ruin payment cells, the initial time-zero right dividend atom plus discounted terminal postpayment caplinear value plus discounted actual Stieltjes cell cash weighted at their right endpoints is bounded by the initial caplinear value and the sum of exact discounted physical prepayment spatial source increments. This is a source-faithful discounted cash and stopped Itô-product ledger, preserving original cap C, original source X and rightLimit D. It supplies the key pathwise inequality required before full/cross Gaussian Taylor and L1 error controls can close B54.
-- source:
--   Per-cell Proved B25 source-faithful signed Stieltjes cash correction times nonnegative original right endpoint discount; Proved B58 genuine initial right atom; Proved B70 exact finite physical discounted source/product telescoping. Weighted finite sum of nonpositive original cell corrections yields the discounted cash source inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB25_original_preruin_interior_caplinear_stieltjes_signed_control
import Theorems.Thm_AvramDividend_Classical_avram_gbB58_original_caplinear_initial_right_atom_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_gbB70_original_physical_discounted_caplinear_prepayment_postpayment_source_telescope
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gbB73_original_interior_caplinear_discounted_physical_strict_dividend_cash_source_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (hsec : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ c →
      b - a ≤ w b - w a)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (n m : ℕ)
    (hPre : ∀ i < m + 1,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * Δ
      s (i + 1) = 0 ∨
      (s (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (s i : ℝ)))
    let V : ℝ → ℝ := fun z =>
      if z ≤ c then w z else w c + (z - c)
    let Y : ℕ → ℝ := fun i =>
      x + X.X (s i) ω - rightLimit D (s i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (s (i + 1)) ω - rightLimit D (s i) ω
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (s i : ℝ) (s (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    rightLimit D 0 ω + e (m + 1) * V (Y (m + 1)) +
      (Finset.range (m + 1)).sum (fun i => e (i + 1) * cash i) ≤
      V x + (Finset.range (m + 1)).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) := by sorry
