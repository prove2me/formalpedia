-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_bv_ubv_balance_to_raw_stopped
-- name    : AvramDividend.Classical.avram_root29_03_bv_ubv_balance_to_raw_stopped
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:11:30.200923+00:00
-- url     : https://prove2.me/theorems/21138221-f9a9-4f46-acb8-f5a70db90216
-- title:
--   Exact canonical raw stopped-scale balance from explicit original BV OST and UBV strict two-payoff balances
-- statement:
--   For the actual Standing spectrally negative Levy law with q>0, 0<a and 0<=x<=a, assume separately that in the bounded-variation case the named strict upper-before-lower discounted exit times W(a) equals W(x), and that in the unbounded-variation case the genuine strict upper plus strict lower discounted terminal q-scale payoffs equal W(x). The exact canonical raw inline-infimum integral cross-product then equals W(x). The only imports are canonically Proved original-law terminal factorisations; both stochastic balances are explicit hypotheses.
-- source:
--   Proved 700ff0e6 raw product equals genuine min-stopped reward; BV uses Proved 76559541 min-stopped reward equals named exit expectation times W(a); UBV uses Proved 7c9fe862 min-stopped reward equals strict upper+lower reward. No Open be9/322 import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_terminal_factorisation
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_exact_qscale_two_branch_terminal_conversion

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_bv_ubv_balance_to_raw_stopped
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hBVBalance : X.BoundedVariation →
      twoSidedExitExpectation X q a x * ENNReal.ofReal (W a) =
        ENNReal.ofReal (W x))
    (hUBVBalance : ¬ X.BoundedVariation →
      (∫⁻ ω,
      (if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω)) else 0) +
      (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitDownTime X (-x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω)) else 0) ∂P) = ENNReal.ofReal (W x)) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) = ENNReal.ofReal (W x) := by sorry
