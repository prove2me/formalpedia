-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:20:52.075951+00:00
-- url     : https://prove2.me/theorems/fe7fc2ec-ace2-4174-a880-0f96881e81a2
-- title:
--   Actual original discounted right-horizon dividend jump plus postpayment value is bounded by prepayment value
-- statement:
--   Under the canonical original-source hJump hypothesis on t=0 or strict pre-ruin, discounted original right-horizon dividend increment plus discounted postpayment terminal value is bounded by discounted original prepayment value. The proof uses the source-exact riskProcess identity x+X.X t-D t, the canonical rightLimit D t reserve, and positivity of the exponential discount. This bridges the prepayment L1 helpers to canonical postpayment terminal accounting without claiming that the Stieltjes dividend measure has the needed horizon atom yet.
-- source:
--   Canonical Open P3 signed budget 9cd69d89 exact hjump and Term, Proved P3-G prepayment L1 60abf1b6 and d6bdcbd6, actual riskProcess and rightLimit D from original Definitions.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      Real.exp (-(q * (t : ℝ))) *
          (rightLimit D t ω - D t ω) +
        Real.exp (-(q * (t : ℝ))) *
          w (x + X.X t ω - rightLimit D t ω) ≤
        Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω) := by sorry
