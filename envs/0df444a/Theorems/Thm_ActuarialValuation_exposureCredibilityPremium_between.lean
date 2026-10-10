-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityPremium_between
-- name    : ActuarialValuation.exposureCredibilityPremium_between
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:18:07.972441+00:00
-- url     : https://prove2.me/theorems/293a6207-4d06-4f78-8591-77f2dab76d95
-- title:
--   Credibility premium remains between experience and collective mean
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. As the credibility weight lies in the unit interval, a lower observed claim rate produces a premium bounded by the observed and collective rates. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \bar x\le\mu\Longrightarrow \bar x\le\widehat\mu(P)\le\mu
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityPremium_between is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityPremium

namespace ActuarialValuation

theorem exposureCredibilityPremium_between
  (EPV VHM P experience collective : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P)
  (hx : experience ≤ collective) :
  experience ≤ exposureCredibilityPremium EPV VHM P experience collective ∧
    exposureCredibilityPremium EPV VHM P experience collective ≤ collective := by sorry

end ActuarialValuation
