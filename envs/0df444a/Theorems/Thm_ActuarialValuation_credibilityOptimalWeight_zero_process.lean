-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityOptimalWeight_zero_process
-- name    : ActuarialValuation.credibilityOptimalWeight_zero_process
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:58:12.455031+00:00
-- url     : https://prove2.me/theorems/97a9e28a-00a1-4a57-bac1-c523a9081ac3
-- title:
--   No conditional claim noise gives full credibility
-- statement:
--   When expected process variance is zero but exposure times hypothetical-mean variance is nonzero, the observed experience already measures the underlying risk mean without conditional noise. The optimal credibility factor equals one.
--
--   **Mathematical statement**
--
--   $$
--   \mathrm{EPV}=0,\ P\mathrm{VHM}\ne0\Rightarrow Z=1
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityOptimalWeight_zero_process
  (p vhm : ℝ) (h : p * vhm ≠ 0) :
  credibilityOptimalWeight p 0 vhm = 1 := by sorry

end ActuarialValuation
