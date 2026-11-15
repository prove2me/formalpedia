-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24w_original_preleft_C2_arbitrary_increment_epsilon_square_bound
-- name    : AvramDividend.Classical.avram_b24w_original_preleft_C2_arbitrary_increment_epsilon_square_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:39:14.444746+00:00
-- url     : https://prove2.me/theorems/e5e227ae-55f4-4872-86f9-d13add78ef64
-- title:
--   Original prepayment reserve C2 Taylor epsilon-square bound for an arbitrary real increment, with no time-order assumption
-- statement:
--   At any actual original prepayment reserve left-limit in a compact positive interior band, and any arbitrary second point of the band, the second-order Taylor remainder is at most epsilon times squared increment when their distance is below a uniform delta. Valid regardless of whether the physical time increment is real subtraction or nonnegative subtraction; retains the original stopped reserve and w.
-- source:
--   Proved original preleft Hessian modulus and Proved compact moving Taylor Lagrange witness, with interval geometry and a square-norm inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ubv_C2_moving_band_taylor_lagrange
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_preleft_hessian_modulus
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b24w_original_preleft_C2_arbitrary_increment_epsilon_square_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbcap : ENNReal.ofReal b < C)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ω (t : ℝ≥0) (y : ℝ),
      let z := Function.leftLim
        (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) t
      z ∈ Icc a b → y ∈ Icc a b → z ≠ y →
      dist y z < δ →
      |w y - taylorWithinEval w 1 (uIcc z y) z y -
        (iteratedDeriv 2 w z * (y-z)^2) / 2| ≤
        ε * (y-z)^2 := by sorry
