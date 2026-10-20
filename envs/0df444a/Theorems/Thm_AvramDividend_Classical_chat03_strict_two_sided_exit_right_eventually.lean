-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_two_sided_exit_right_eventually
-- name    : AvramDividend.Classical.chat03_strict_two_sided_exit_right_eventually
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:21:49.470359+00:00
-- url     : https://prove2.me/theorems/c61df2ed-f0c6-4e7d-b385-d34f1b0ec96d
-- title:
--   Strict two-sided Lévy crossing persists immediately to the right by sample-path right-continuity
-- statement:
--   Let X be the exact published spectrally negative Lévy process, ω a sample path, t≥0, and lower and upper real thresholds. If at t the reserve is strictly below lower or strictly above upper, then for times s immediately to the right of t in the relative neighbourhood filter of [t,∞), it stays strictly below lower or strictly above upper. This follows directly from the sample-path right-continuity field of SpectrallyNegativeLevy and openness of the strict exit set (-∞,lower)∪(upper,∞). It is the pure pathwise input for proving that dense dyadic discrete first-crossing times converge to the continuous strict exit infimum. It requires no right-continuous filtration, Markov property or no-positive-jumps strengthening.
-- source:
--   Exact pinned Formalpedia SpectrallyNegativeLevy.rightCont field and pinned Mathlib IsOpen.mem_nhds, Filter.Tendsto.eventually, revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Topology.Order.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_two_sided_exit_right_eventually
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower upper : ℝ)
    (h : X.X t ω < lower ∨ upper < X.X t ω) :
    ∀ᶠ s in 𝓝[Set.Ici t] t,
      X.X s ω < lower ∨ upper < X.X s ω := by sorry
