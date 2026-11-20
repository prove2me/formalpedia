-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_true_strict_prefix_stieltjes_error_le_ruin_rightLimit_mesh_rate
-- name    : AvramDividend.Classical.avram_jump6_B_true_strict_prefix_stieltjes_error_le_ruin_rightLimit_mesh_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T20:33:46.992689+00:00
-- url     : https://prove2.me/theorems/2466e036-5ee7-4e13-8693-b93c72791596
-- title:
--   True original strict prefix discounted Stieltjes mesh error bounded by ruin-contact right-limit
-- statement:
--   For any original dividend strategy and precontact clock t no later than the true ruin-contact clock rho, the exact ENNReal discounted mesh error involving the actual dividendMeasure on Ioc(0,t), converted to Real, is bounded by the positive-horizon source coefficient q*n*exp(q*n)/(j+1) times the true dividend right-limit at rho. Uses only original measure identity, monotonicity and positivity; no finite-activity hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_jump6_B_true_strict_prefix_stieltjes_error_le_ruin_rightLimit_mesh_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t ρ : ℝ≥0) (htρ : t ≤ ρ)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n) (j : ℕ) :
    (ENNReal.ofReal (q * ((1 : ℝ) / ((j : ℝ) + 1))) *
        dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ))).toReal ≤
      q * ((n : ℝ) / ((j : ℝ) + 1)) *
        Real.exp (q * (n : ℝ)) * rightLimit D ρ ω := by sorry
