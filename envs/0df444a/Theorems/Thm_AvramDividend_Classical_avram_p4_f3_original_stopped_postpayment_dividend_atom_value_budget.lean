-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget
-- name    : AvramDividend.Classical.avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:18:04.085291+00:00
-- url     : https://prove2.me/theorems/b57dad84-79b5-4113-89a2-2ac9d82cac09
-- title:
--   Original stopped-clock prepayment potential pays postpayment right dividend atom
-- statement:
--   Directly from the exact secant dividend assumption used by the canonical original stopped UBV component theorem, at time zero or before ruin, postpayment reserve potential plus the right dividend cash atom is bounded by prepayment potential. This handles original dividend jumps without changing the reserve source convention and is an importable stopped-clock adapter.
-- source:
--   Accepted public e0c6f36d original right dividend jump reserve identity and original canonical hJump secant inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget
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
    (ω : Ω) (t : ℝ≥0)
    (hTime : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    w (x + X.X t ω - rightLimit D t ω) +
      (rightLimit D t ω - D t ω) ≤
        w (riskProcess X x D t ω) := by sorry
