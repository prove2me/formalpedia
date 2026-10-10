-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityOptimalWeight_zero_heterogeneity
-- name    : ActuarialValuation.credibilityOptimalWeight_zero_heterogeneity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:57:46.439967+00:00
-- url     : https://prove2.me/theorems/8c683821-6790-40c7-b72e-8759f7777962
-- title:
--   No between-risk heterogeneity implies zero experience credibility
-- statement:
--   If the hypothetical risk means do not vary, individual historical experience contains no signal of a persistent difference from the population mean. For positive process variance, the optimal credibility factor is zero regardless of exposure.
--
--   **Mathematical statement**
--
--   $$
--   \mathrm{VHM}=0,\ \mathrm{EPV}>0\Rightarrow Z=0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityOptimalWeight_zero_heterogeneity
  (p epv : ℝ) (he : 0 < epv) :
  credibilityOptimalWeight p epv 0 = 0 := by sorry

end ActuarialValuation
