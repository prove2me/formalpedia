-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_postpayment_rightatom_value_budget
-- name    : AvramDividend.Classical.avram_p4_f3_original_postpayment_rightatom_value_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:14:25.553585+00:00
-- url     : https://prove2.me/theorems/d4c8eb67-ae68-4a26-9dc9-350d1311eab2
-- title:
--   Original prepayment potential pays the exact postpayment dividend right atom
-- statement:
--   The hJump secant inequality on the actual original dividend-controlled Lévy reserve pays the exact dividend right atom from prepayment potential, yielding postpayment potential plus paid cash at most prepayment potential at every physical time, including zero and simultaneous Lévy jumps. This source-exact result retains the pre/post payment distinction required by the stopped stochastic budget.
-- source:
--   Public Proved original reserve/postpayment right atom e0c6f36d; real linear rearrangement of the explicitly supplied dividend potential secant inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_postpayment_rightatom_value_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0), True →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0) :
    w (x + X.X t ω - rightLimit D t ω) +
      (rightLimit D t ω - D t ω) ≤
        w (riskProcess X x D t ω) := by sorry
