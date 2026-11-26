-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stageClock_le_logb
-- name    : FirstPassageLinearTransport.stageClock_le_logb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:22:57.106343+00:00
-- url     : https://prove2.me/theorems/78adf2e2-6b94-561f-9a79-0fd9b8977e91
-- title:
--   First Passage Linear Transport: stage Clock le logb
-- statement:
--   The accumulated shortcut clock has the expected geometric leading term;
--   the deliberately coarse startup error is only quadratic in the stage count.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L482-L544
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Bootstrap.lean#L482-L544

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section

theorem FirstPassageLinearTransport.stageClock_le_logb
    {r eta : ℝ} (p : StageSetup r eta) {R n : ℕ}
    (hn : 0 < n) (hnSet : n ∈ bootstrapSet p R) :
    (stageClock p R n : ℝ) ≤
      clockGeom r R * Real.logb 2 n +
        (R : ℝ) ^ 2 * Real.logb 2 (stageK p) := by sorry
