-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityPremium_shift
-- name    : ActuarialValuation.exposureCredibilityPremium_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:17:53.282653+00:00
-- url     : https://prove2.me/theorems/ced46763-43df-4eaf-b392-1bf585601438
-- title:
--   Premium deviation from collective mean is credibility-weighted deviation
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. The difference between the credibility estimate and the portfolio mean equals weight times the underlying experience deviation. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \widehat\mu(P)-\mu=Z(P)(\bar x-\mu)
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityPremium_shift is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight
import Definitions.Def_actuarial_exposureCredibilityPremium

namespace ActuarialValuation

theorem exposureCredibilityPremium_shift
  (EPV VHM P experience collective : ℝ) :
  exposureCredibilityPremium EPV VHM P experience collective - collective =
    exposureCredibilityWeight EPV VHM P * (experience - collective) := by sorry

end ActuarialValuation
