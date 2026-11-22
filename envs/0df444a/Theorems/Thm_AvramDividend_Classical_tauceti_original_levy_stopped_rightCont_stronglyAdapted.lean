-- Prove2me | Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stopped_rightCont_stronglyAdapted
-- name    : AvramDividend.Classical.tauceti_original_levy_stopped_rightCont_stronglyAdapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:02:49.650129+00:00
-- url     : https://prove2.me/theorems/c78346ec-04b7-485c-9c52-865a036bb83c
-- title:
--   Original Lévy process stopped under the right-continuous filtration is strongly adapted
-- statement:
--   For the original Levy process with no additional probabilistic assumptions, stopping at any stopping time of the right-continuous filtration gives a strongly adapted stopped process in that filtration. Useful at every positive-clock stopped Ito-Meyer localisation of the original Avram surplus driver.
-- source:
--   TauCetiProject/TauCeti Probability/Martingale/ContinuousStopping.lean and Probability/Process/Progressive.lean, Apache-2.0, The Tau Ceti contributors; proof reuses Proved Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive and pinned Mathlib IsStronglyProgressive.stronglyAdapted_stoppedProcess. Source context: Avram original positive-clock Ito witness 6b50f324-ce17-458d-995b-8dcff5d9e075.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
open MeasureTheory Filter Set TopologicalSpace AvramDividend.Classical
open scoped NNReal Topology

theorem AvramDividend.Classical.tauceti_original_levy_stopped_rightCont_stronglyAdapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    StronglyAdapted 𝓕.rightCont (stoppedProcess X.X τ) := by sorry
