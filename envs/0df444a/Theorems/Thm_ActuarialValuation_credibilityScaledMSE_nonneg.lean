-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityScaledMSE_nonneg
-- name    : ActuarialValuation.credibilityScaledMSE_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:13:56.414568+00:00
-- url     : https://prove2.me/theorems/2c70d1f9-93f9-4b14-9fde-e312a059cdba
-- title:
--   Exposure-scaled credibility error is nonnegative
-- statement:
--   The scaled prediction loss is a sum of nonnegative variance coefficients times squared deviations of the credibility weight. For nonnegative exposure and variance parameters, the prediction-error objective cannot be negative for any real weight.
--
--   **Mathematical statement**
--
--   $$
--   P,\mathrm{EPV},\mathrm{VHM}\ge0\Rightarrow P\,\mathrm{MSE}(z)\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityScaledMSE

namespace ActuarialValuation

theorem credibilityScaledMSE_nonneg
  (p epv vhm z : ℝ)
  (hp : 0 ≤ p) (he : 0 ≤ epv) (hv : 0 ≤ vhm) :
  0 ≤ credibilityScaledMSE p epv vhm z := by sorry

end ActuarialValuation
