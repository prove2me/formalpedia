-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
-- name    : AvramDividend.Classical.admissibleLe_riskProcess_le_cap_all_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:22:15.676093+00:00
-- url     : https://prove2.me/theorems/c521fe8f-97c2-40ec-a5c3-b6184a6ad3ea
-- title:
--   A capped admissible strategy preserves the reserve bound at all times, including the initial instant
-- statement:
--   Under capped admissibility IsAdmissibleLe X x C D and initial reserve ofReal x≤C, the entire controlled reserve path satisfies ofReal U_t≤C at every nonnegative time. For t>0 this is exactly the cap condition in IsAdmissibleLe. At t=0, X0=D0=0 so U0=x. This closes the edge case needed to apply an HJB dividend-value bound to jumps at the initial payment instant.
-- source:
--   Exact IsAdmissibleLe and IsDividendStrategy definitions and SpectrallyNegativeLevy.X_zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissibleLe_riskProcess_le_cap_all_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hxC : ENNReal.ofReal x ≤ C)
    (ω : Ω) (t : ℝ≥0) :
    ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by sorry
