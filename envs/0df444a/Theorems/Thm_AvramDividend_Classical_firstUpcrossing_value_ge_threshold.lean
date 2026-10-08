-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_ge_threshold
-- name    : AvramDividend.Classical.firstUpcrossing_value_ge_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:14:27.875063+00:00
-- url     : https://prove2.me/theorems/42162a90-c986-45bc-8120-e8e89d8a3d31
-- title:
--   Right continuity forces a finite first strict upcrossing to reach the threshold
-- statement:
--   For an everywhere right-continuous path and a finite first strict upcrossing time u of level b≥0, the sample-path value at u cannot be less than b. Otherwise right continuity implies that all path values sufficiently near u from the right remain below b. Combined with the infimum definition of the first strict upcrossing, this would show that every strict exceedance occurs at least some positive distance after u, contradicting the infimum being u. This isolates the right-continuity half of the firstUpcrossing_value_eq_threshold theorem and needs no assumptions about jumps, Markov property, or independent increments.
-- source:
--   Canonical SpectrallyNegativeLevy.rightCont and first-upcrossing time definition; order/topology of NNReal/ENNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem firstUpcrossing_value_ge_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    b ≤ X.X u ω := by sorry
end AvramDividend.Classical
