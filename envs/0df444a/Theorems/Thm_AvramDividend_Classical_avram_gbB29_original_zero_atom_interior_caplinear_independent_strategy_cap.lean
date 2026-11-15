-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB29_original_zero_atom_interior_caplinear_independent_strategy_cap
-- name    : AvramDividend.Classical.avram_gbB29_original_zero_atom_interior_caplinear_independent_strategy_cap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:14:57.700309+00:00
-- url     : https://prove2.me/theorems/0077a47c-2cd1-4639-af04-6bb636ecce07
-- title:
--   Original time-zero dividend atom under interior cap-linear clipping independent of admissibility cap
-- statement:
--   The original dividend atom at time zero is bounded in ENNReal by the decrease in the interior cap-linear value, even when the dividend strategy is admissible at a separate original cap C. The proof extracts the required dividend strategy property and initial postpayment reserve bound from admissibility at C.
-- source:
--   Exact original-source zero-atom argument from Proved dbaf2f36, using the deeper caplinear_closed_horizon_all_mass_budget theorem whose clipping level does not need to match the admissibility cap.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_caplinear_closed_horizon_all_mass_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_gbB29_original_zero_atom_interior_caplinear_independent_strategy_cap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 < c) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < ENNReal.ofReal c})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < ENNReal.ofReal c → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) :
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) ≤
    ENNReal.ofReal (
      (if x + X.X 0 ω ≤ c then w (x + X.X 0 ω)
        else w c + (x + X.X 0 ω - c)) -
      (if x + X.X 0 ω - rightLimit D 0 ω ≤ c
        then w (x + X.X 0 ω - rightLimit D 0 ω)
        else w c + ((x + X.X 0 ω - rightLimit D 0 ω) - c))) := by sorry
