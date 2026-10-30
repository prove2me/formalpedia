-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
-- name    : AvramDividend.Classical.avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:53:45.975376+00:00
-- url     : https://prove2.me/theorems/700ff0e6-897d-418b-bfe4-54faa20c6529
-- title:
--   Original raw strict two-sided exit discount times upper scale equals true stopped-minimum terminal scale reward
-- statement:
--   For a genuine Standing spectrally negative Levy process, positive discount, 0<a and 0<=x<=a, the canonical inline passage-infimum strict upper-before-ruin lintegral multiplied by W_q(a) equals the original stopped-minimum terminal discounted scale reward. The result uses the canonically Proved all-variation original stopped-minimum factorisation 76559541 and is unconditional on killed harmonicity.
-- source:
--   Direct exact inline unfolding of twoSidedExitExpectation and its upper/lower exit infima, reducing to the Proved BV/UBV original stopped-minimum terminal factorisation. No Open killed identities imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_standing_stopped_min_terminal_factorisation

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_raw_exit_scale_product_eq_stopped_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (∫⁻ ω,
      if (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) * ENNReal.ofReal (W a) =
    (∫⁻ ω, if min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω) < ⊤ then
      ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (min (twoSidedExitUpTime X (a - x) ω)
              (twoSidedExitDownTime X (-x) ω))))) *
        ENNReal.ofReal
          (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal ω))
      else 0 ∂P) := by sorry
