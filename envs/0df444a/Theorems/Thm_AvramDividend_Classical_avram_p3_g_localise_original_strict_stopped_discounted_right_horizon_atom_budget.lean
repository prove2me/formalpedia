-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_strict_stopped_discounted_right_horizon_atom_budget
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_strict_stopped_discounted_right_horizon_atom_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:50:08.242547+00:00
-- url     : https://prove2.me/theorems/ef7f405e-8f6b-4ba1-af13-e4bdf0095b62
-- title:
--   Canonical strict-ruin stopped right-horizon dividend atom and postpayment value satisfy original discounted inequality
-- statement:
--   The original discount jump budget remains true after applying the canonical strict pre-ruin indicator at each deterministic time. On the true strict event, the Proved original discounted horizon atom lemma applies; outside, both sides are exactly zero. This directly gives the pointwise stopped integrand bound needed to transfer P3-G prepayment L1 to P3-F postpayment terminal accounting, without asserting unproved dividendMeasure atom identities.
-- source:
--   Canonical original signed budget 9cd69d89 Term strict-ruin indicator and hjump; P3-G source discounted atom helper.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_strict_stopped_discounted_right_horizon_atom_budget
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
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
            (rightLimit D t ω - D t ω) +
          Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω)
       else 0) ≤
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω)
       else 0) := by sorry
