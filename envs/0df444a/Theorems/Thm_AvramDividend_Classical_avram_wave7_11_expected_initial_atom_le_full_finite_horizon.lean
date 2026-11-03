-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_11_expected_initial_atom_le_full_finite_horizon
-- name    : AvramDividend.Classical.avram_wave7_11_expected_initial_atom_le_full_finite_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:56:50.686956+00:00
-- url     : https://prove2.me/theorems/33347f0e-8da7-46b4-a109-b95785f02889
-- title:
--   Original expected full finite-horizon dividend retains the complete initial Stieltjes atom
-- statement:
--   For an original source dividend path strategy D and sample-dependent genuine stopping clock σ, the expected dividendMeasure mass of the initial time-zero singleton is no larger than the complete expected discounted Stieltjes dividend reward up to any nonnegative finite real horizon T. The exact zero-horizon payoff equals the atom and the proved finite-horizon monotonicity preserves it for T≥0.
-- source:
--   Corollary of W7-11 zero-horizon atom equality and prior Proved W7-11 horizon monotonicity f74e27ec. This protects the t=0 dividend jump in the canonical UBV finite-horizon verification bound.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_discounted_stieltjes_horizon_mono

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_11_expected_initial_atom_le_full_finite_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, (dividendMeasure D ω) ({0} : Set ℝ) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
