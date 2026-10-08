-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_attains_peak
-- name    : AvramDividend.Classical.firstUpcrossing_attains_peak
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:54:49.840468+00:00
-- url     : https://prove2.me/theorems/473109a5-7650-47ba-b397-29e7480e709e
-- title:
--   First strict upcrossing by a process with no positive jumps attains the barrier as a running-supremum peak
-- statement:
--   Fix a càdlàg sample path of a spectrally negative Lévy process started at zero. For b≥0 let τ_b^+ be the infimum of times t with X_t>b, with infinity for an empty set. Whenever the strict upcrossing time equals a finite embedded time u, the absence of positive jumps and path right-continuity force X_u=b. No earlier value can exceed b, so the raw running supremum on [0,u] is exactly b and is attained at u. The statement includes the endpoint b=0,u=0 and does not assume a stopping-time law or strong Markov property. It is the missing pathwise threshold-attainment prerequisite for the already Proved post-threshold barrierStrategy restart identity.
-- source:
--   Avram, Palmowski, Pistorius (2007) two-sided first-passage fluctuation argument and Proposition 1, no positive overshoot for spectrally negative Lévy processes; the canonical SpectrallyNegativeLevy.rightCont, leftLim, noPosJumps, X_zero fields.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem firstUpcrossing_attains_peak
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    X.X u ω = b ∧
      sSup ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u) =
        X.X u ω := by sorry

end AvramDividend.Classical
