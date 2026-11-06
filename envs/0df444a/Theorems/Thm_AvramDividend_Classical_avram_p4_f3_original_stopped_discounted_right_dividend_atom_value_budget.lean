-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_discounted_right_dividend_atom_value_budget
-- name    : AvramDividend.Classical.avram_p4_f3_original_stopped_discounted_right_dividend_atom_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:34:08.756926+00:00
-- url     : https://prove2.me/theorems/a77b0e24-2411-4cf2-bd6d-76fe4c2d820d
-- title:
--   Original stopped discounted right dividend atom pays from prepayment potential
-- statement:
--   At time zero or strictly before ruin, the canonical original hJump secant inequality remains valid after multiplying by the actual positive exponential discount factor. Discounted postpayment potential plus discounted right dividend cash is bounded by discounted prepayment potential. This directly matches finite-horizon Ito terminal and dividend-cash terms without assuming a zero dividend right atom.
-- source:
--   Public Proved b57dad84 original stopped right dividend atom budget and positivity of real exponential.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_stopped_discounted_right_dividend_atom_value_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (hTime : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) *
      w (x + X.X t ω - rightLimit D t ω) +
      Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) ≤
      Real.exp (-(q * (t : ℝ))) *
        w (riskProcess X x D t ω) := by sorry
