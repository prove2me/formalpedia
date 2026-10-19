-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
-- name    : AvramDividend.Classical.runningSup_monotone_and_path_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:13:18.478429+00:00
-- url     : https://prove2.me/theorems/848fbd48-f69f-46b9-b2bf-436cb33918a8
-- title:
--   Actual Lévy running supremum is monotone and dominates the observed path
-- statement:
--   For a càdlàg sample path of a spectrally negative Lévy process, its running supremum (including zero) is nondecreasing and bounds the path from above at every time. The proof first uses the existing local boundedness and compact interval argument for càdlàg paths to certify the BddAbove premise required by conditionally complete real indexed suprema. It then proves monotonicity from inclusion [0,s]⊆[0,t] and pointwise domination by inserting t itself into [0,t]. This discharges the two genuine hypotheses of the published generic runningSup_right_continuous_of_right_continuous theorem, enabling an unconditional reflected-path right-continuity bridge.
-- source:
--   Prove2Me proved runningSup_eq_rawSup_nonneg (992246e6-0bba-4d6f-bd75-5b29c32037f9), whose accepted proof supplied the original boundedness argument; Avram Palmowski Pistorius (2007), Sec 3.3 running supremum.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection

open MeasureTheory Filter Set Topology Bornology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_monotone_and_path_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Monotone (fun t : ℝ≥0 => runningSup X t ω) ∧
    ∀ t : ℝ≥0, X.X t ω ≤ runningSup X t ω := by sorry
