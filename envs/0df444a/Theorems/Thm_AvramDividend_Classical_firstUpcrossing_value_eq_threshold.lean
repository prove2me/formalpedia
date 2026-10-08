-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
-- name    : AvramDividend.Classical.firstUpcrossing_value_eq_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:57:10.947025+00:00
-- url     : https://prove2.me/theorems/014436e7-36d8-45ea-8ca6-bc6917b7788c
-- title:
--   No-positive-jump paths attain their first finite strict upcrossing level without overshoot
-- statement:
--   For a càdlàg, spectrally negative Lévy path with X_0=0, consider the infimum of times it strictly exceeds b≥0. On paths for which this passage time is finite and represented by u, no-positive-jump paths must attain X_u=b: right continuity excludes an undershoot and a positive jump across b is ruled out by the noPosJumps field and the left limit at positive u. At u=0, the initial value X_0=0 and right-continuity force b=0. This theorem isolates the nontrivial analytic endpoint part of proving that first strict upcrossing is an attained running-supremum peak, and makes no Markov or stopping-time-law assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), first-passage upward creeping and no positive overshoot, Proposition 1; canonical SpectrallyNegativeLevy.rightCont, leftLim, noPosJumps, X_zero fields.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical
theorem firstUpcrossing_value_eq_threshold
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    X.X u ω = b := by sorry
end AvramDividend.Classical
