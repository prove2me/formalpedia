-- Prove2me | Theorems.Thm_DensityExtension_ceilApprox_coe
-- name    : DensityExtension.ceilApprox_coe
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:49:10.761001+00:00
-- url     : https://prove2.me/theorems/d56b122b-e3d3-4a3b-b60c-34b584dc3779
-- title:
--   LeanLevy: DensityExtension.ceilApprox_coe
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L139

import Init
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open scoped NNReal

theorem DensityExtension.ceilApprox_coe (t : ℝ≥0) (m : ℕ) :
    (DensityExtension.ceilApprox t m : ℝ) = ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := by sorry
