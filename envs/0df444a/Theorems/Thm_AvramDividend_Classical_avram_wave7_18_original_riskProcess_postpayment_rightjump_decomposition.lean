-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
-- name    : AvramDividend.Classical.avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:23:34.022117+00:00
-- url     : https://prove2.me/theorems/e0c6f36d-6f62-4f86-b4cf-15aced96b92b
-- title:
--   Exact original riskProcess and right dividend-jump postpayment reserve decomposition
-- statement:
--   At every time t≥0, including t=0 and simultaneous Lévy/dividend jumps, for the ORIGINAL Lévy source SpectrallyNegativeLevy P 𝓕 and original admissible dividend strategy D, riskProcess X x D t ω equals x+X.X t ω-D t ω, which is the post-payment right-limit controlled reserve Z_t=x+X.X t ω-rightLimit D t ω plus the right dividend payment rightLimit D t ω-D t ω. Consequently riskProcess minus the right dividend payment equals Z_t. Both identities are exact pathwise algebra; they make the relationship between the paper's reserve value before a right dividend jump and the localisation post-payment reserve explicit. They do not equate the predictable left-limit reserve with the riskProcess at a simultaneous Lévy jump.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    riskProcess X x D t ω -
      (rightLimit D t ω - D t ω) =
      x + X.X t ω - rightLimit D t ω ∧
    riskProcess X x D t ω =
      (x + X.X t ω - rightLimit D t ω) +
      (rightLimit D t ω - D t ω) := by sorry
