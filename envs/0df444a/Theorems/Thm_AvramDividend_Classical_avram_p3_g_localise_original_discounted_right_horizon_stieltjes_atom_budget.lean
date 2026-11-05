-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_stieltjes_atom_budget
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_discounted_right_horizon_stieltjes_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:50:38.203161+00:00
-- url     : https://prove2.me/theorems/6e015b34-1709-4fb9-b393-df1fc72b5a3d
-- title:
--   Original strict-ruin and zero-time Stieltjes horizon singleton plus postpayment terminal HJB drop
-- statement:
--   The exact original Stieltjes measure at the active right-horizon singleton, including time zero, has discounted cash equal to exp(-qS) times the canonical right dividend jump. Adding the original post-dividend terminal reserve value is bounded by the discounted pre-dividend reserve value, by the canonical hJump. No surrogate reserve, extra axiom, diffuse-boundary mass claim, or measure domination assumption.
-- source:
--   Original dividendMeasure_singleton_eq_rightLimit_sub, paymentTimes_terminal_active_lintegral_eq_atom, dividendStrategy_le_rightLimit and P3-G source discounted right-horizon jump lemma; canonical signed budget 9cd69d89.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_terminal_active_lintegral_eq_atom
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_discounted_right_horizon_stieltjes_atom_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (S : ℝ≥0),
      (S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω) →
      (∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
          ({(S : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω) ≤
      Real.exp (-(q * (S : ℝ))) *
        w (riskProcess X x D S ω) := by sorry
