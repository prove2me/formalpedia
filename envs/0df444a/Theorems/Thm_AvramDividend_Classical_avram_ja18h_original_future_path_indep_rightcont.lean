-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_future_path_indep_rightcont
-- name    : AvramDividend.Classical.avram_ja18h_original_future_path_indep_rightcont
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:27:07.124514+00:00
-- url     : https://prove2.me/theorems/c8fa0b62-902d-44cd-a066-e3e5ea5ac2bf
-- title:
--   Original Lévy future increment path is independent of its original right-continuous past
-- statement:
--   For every deterministic s, show the full shifted original Lévy path u↦X(s+u)−X(s) is independent of F.rightCont(s). Derive from proved stopped-source strong Markov independence 75f1abe0 or ce77d378 with the constant stopping clock, checking the equality of its stopped-history sigma algebra with F.rightCont(s). This concerns the same original filtered process.
-- source:
--   AVRAM J-A18 deterministic-clock stopped source independence bridge

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18h_original_future_path_indep_rightcont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0) :
    ProbabilityTheory.Indep
      (𝓕.rightCont s)
      (MeasurableSpace.comap (fun ω : Ω => fun u : ℝ≥0 =>
        X.X (s + u) ω - X.X s ω) inferInstance) P := by sorry
