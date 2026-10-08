-- Prove2me | Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le
-- name    : AvramDividend.Classical.path_value_le_of_strict_prefix_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:06:38.175976+00:00
-- url     : https://prove2.me/theorems/aba62bfd-a593-49f2-a043-9a980b6b07b8
-- title:
--   No positive jumps preserve an upper bound at the endpoint of a strict time prefix
-- statement:
--   For a càdlàg process with no positive jumps and initial value zero, if X_t≤b for every t<u, then X_u≤b, provided b≥0. If u=0 this follows from X_0=0. If u>0, the left limit is bounded by b by the prefix bound, and no-positive-jumps gives X_u≤X_{u−}. This isolates the upper inequality required for firstUpcrossing_value_eq_threshold once the separately published firstUpcrossing_prethreshold_le is proved.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3 spectrally negative paths; SpectrallyNegativeLevy.leftLim, noPosJumps and X_zero. Independent reusable source-faithful child of AvramDividend.Classical.firstUpcrossing_value_eq_threshold (014436e7-36d8-45ea-8ca6-bc6917b7788c).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.path_value_le_of_strict_prefix_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hpre : ∀ t : ℝ≥0, t < u → X.X t ω ≤ b) :
    X.X u ω ≤ b := by sorry
