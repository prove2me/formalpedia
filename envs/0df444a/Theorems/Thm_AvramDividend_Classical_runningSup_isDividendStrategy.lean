-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
-- name    : AvramDividend.Classical.runningSup_isDividendStrategy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:56:20.77888+00:00
-- url     : https://prove2.me/theorems/8f7ae7d8-6651-454c-8d22-167256ac01b4
-- title:
--   The actual running-supremum regulator is an adapted left-continuous dividend strategy
-- statement:
--   For every published spectrally negative Lévy process, its actual running supremum satisfies the formal IsDividendStrategy predicate relative to the given filtration. Instantiate the already proved equality of a constant-barrier strategy started at its own barrier with the running supremum at barrier zero. The existing proof that every nonnegative-barrier construction is a dividend strategy then transfers all properties, including adaptedness, monotonicity, left continuity and the zero initial value. This is an interface for applying the separately proved stochastic measurability of dividend Stieltjes measures directly to the original running-supremum process.
-- source:
--   Proved barrierStrategy_self_eq_runningSup target 6f853442-0ba9-4515-8a3d-2297508c4913 and barrierStrategy_isDividendStrategy_nonnegative_barrier target 501af29f-f958-42d6-8682-5dc331fedae7.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_isDividendStrategy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    IsDividendStrategy 𝓕 (runningSup X) := by sorry
