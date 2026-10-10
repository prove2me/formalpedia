-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityPremium_zero
-- name    : ActuarialValuation.exposureCredibilityPremium_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:47:28.828985+00:00
-- url     : https://prove2.me/theorems/8423e76b-80a0-4392-a504-e20585279ed9
-- title:
--   With zero exposure the premium reverts to collective mean
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. When there are no credible risk-specific observations, the unbiased collective mean provides the entire per-unit estimated premium. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \widehat\mu(0)=\mu
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityPremium_zero is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityPremium

namespace ActuarialValuation

theorem exposureCredibilityPremium_zero
  (EPV VHM experience collective : ℝ) (hE : 0 < EPV) :
  exposureCredibilityPremium EPV VHM 0 experience collective = collective := by sorry

end ActuarialValuation
