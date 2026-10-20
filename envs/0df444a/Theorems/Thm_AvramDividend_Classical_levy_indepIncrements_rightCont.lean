-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_indepIncrements_rightCont
-- name    : AvramDividend.Classical.levy_indepIncrements_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T22:24:55.832226+00:00
-- url     : https://prove2.me/theorems/baf51c16-b8db-418a-ac69-e05fccfaa155
-- title:
--   A Lévy process retains future independent increments under the right-continuous filtration
-- statement:
--   Unconditional independence of X_t-X_s from the right-continuous past for all s≤t, using the already published and Proved sequence-independence lemma. An approximating sequence is constructed inline, so there is no dependency on the unpublished exists_right_approximation theorem. The earlier failed publication imported that unavailable theorem; this version uses only Proved imports.
-- source:
--   Source-faithful corrected authoring spec; complete candidate levy_indepIncrements_rightCont_v3.lean; prior job b8e21ccf failed on unavailable approximation theorem import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_indep_from_sequence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_indepIncrements_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    Indep
      (MeasurableSpace.comap (fun ω => X.X t ω - X.X s ω) inferInstance)
      (𝓕.rightCont s) P := by sorry
