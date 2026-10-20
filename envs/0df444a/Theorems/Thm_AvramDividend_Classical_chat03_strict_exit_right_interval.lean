-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_strict_exit_right_interval
-- name    : AvramDividend.Classical.chat03_strict_exit_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:46:36.384301+00:00
-- url     : https://prove2.me/theorems/f0afde4a-46d2-43ca-9485-019f49c61fa3
-- title:
--   Every strict Lévy exit has a concrete right interval of persistent strict exit
-- statement:
--   Let X be an official spectrally negative Lévy process and ω one of its right-continuous sample paths. If at a nonnegative time t the path is strictly below lower or strictly above upper, there exists a later time u>t such that at every s in [t,u) the same strict exit disjunction holds. Unlike an abstract neighbourhood eventuality, this result provides explicit order interval witnesses needed to combine the deterministic ceiling-grid bracket with sample-path persistence. It follows from the previously Proved right-neighbourhood strict exit theorem and the pinned order-topology interval-basis lemma; it imposes no filtration right-continuity, Markov property or q-scale harmonicity.
-- source:
--   Previously Proved AvramDividend.Classical.chat03_strict_two_sided_exit_right_eventually c61df2ed-f0c6-4e7d-b385-d34f1b0ec96d and pinned Mathlib Topology.Order.LeftRightNhds exists_Ico_subset_of_mem_nhds' at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_strict_two_sided_exit_right_eventually
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_strict_exit_right_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (lower upper : ℝ)
    (h : X.X t ω < lower ∨ upper < X.X t ω) :
    ∃ u : ℝ≥0, t < u ∧
      ∀ s : ℝ≥0, t ≤ s → s < u →
        X.X s ω < lower ∨ upper < X.X s ω := by sorry
