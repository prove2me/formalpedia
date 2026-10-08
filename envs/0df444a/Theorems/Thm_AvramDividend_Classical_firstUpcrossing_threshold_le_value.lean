-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_le_value
-- name    : AvramDividend.Classical.firstUpcrossing_threshold_le_value
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:06:26.218966+00:00
-- url     : https://prove2.me/theorems/a5a18b2e-1a6b-45cb-9da9-054a962d5a38
-- title:
--   At finite first strict upcrossing, right continuity gives the lower threshold bound
-- statement:
--   Given finite strict first upcrossing time u of threshold b, right continuity of the Lévy path implies the value at u is at least b. If it were below b, right continuity would keep the process below b for a short interval after u, contradicting the defining infimum. This is the lower inequality of firstUpcrossing_value_eq_threshold and is independent of the no-positive-jump property.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 3 first-passage convention, and the right-continuity field of SpectrallyNegativeLevy. Direct source-faithful child of AvramDividend.Classical.firstUpcrossing_value_eq_threshold (014436e7-36d8-45ea-8ca6-bc6917b7788c).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.firstUpcrossing_threshold_le_value
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (t : ℝ≥0) (_ : b < X.X t ω), (t : ℝ≥0∞))) :
    b ≤ X.X u ω := by sorry
