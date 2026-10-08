-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_measurable
-- name    : AvramDividend.Classical.riskProcess_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:43:21.859975+00:00
-- url     : https://prove2.me/theorems/609c0194-6622-495b-8efe-1e75a233813f
-- title:
--   Measurability of the controlled reserve at a fixed time
-- statement:
--   At each deterministic time t, the controlled reserve x + X_t - D_t is measurable in the sample point because both X and the dividend strategy D are adapted.
-- source:
--   Elementary measurability helper for the ruin-time and Proposition 4(i) verification arguments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (t : ℝ≥0) :
    Measurable (fun ω => riskProcess X x D t ω) := by sorry
