-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_barrier_at_firstUpcrossing_eq_barrier
-- name    : AvramDividend.Classical.riskProcess_barrier_at_firstUpcrossing_eq_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:46:12.137254+00:00
-- url     : https://prove2.me/theorems/7bf0c055-e04d-4ae9-bb71-2df611133efa
-- title:
--   Controlled surplus equals the barrier at its first finite upward crossing
-- statement:
--   At a finite strict upward-passage time u of the threshold a−x≥0, the controlled surplus under the barrier strategy is exactly a. Spectral negativity gives X_u=a−x with no overshoot. The barrier regulator has paid zero dividends through u, including the passage instant, hence U^a_u=x+X_u−L^a_u=a. This provides the exact restart state for the strong-Markov barrier-value factorisation and handles a potential stopping-time dividend atom. It should be proved by combining the Proved firstUpcrossing_value_eq_threshold with the separately published zero-dividend-at-upcrossing child, independently of any dividend-value expectation identity.
-- source:
--   Avram, Palmowski, Pistorius (2007), Proposition 1 pre-passage strong-Markov regeneration; Def_AvramDividend_Classical_DividendStrategy riskProcess and barrierStrategy; Proved firstUpcrossing_value_eq_threshold.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_barrier_at_firstUpcrossing_eq_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞))) :
    riskProcess X x (barrierStrategy X x a) u ω = a := by sorry
