-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityWeight_lt_one
-- name    : ActuarialValuation.exposureCredibilityWeight_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T16:46:58.977584+00:00
-- url     : https://prove2.me/theorems/3ea35a25-0426-4836-b239-b08fdb0f1a63
-- title:
--   Positive process noise makes credibility strictly less than one
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. Finite exposure cannot imply full credibility when nonzero process noise remains in the insured risk. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   \mathrm{EPV}>0,\ P,\mathrm{VHM}\ge0\Longrightarrow Z(P)<1
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityWeight_lt_one is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight

namespace ActuarialValuation

theorem exposureCredibilityWeight_lt_one
  (EPV VHM P : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  exposureCredibilityWeight EPV VHM P < 1 := by sorry

end ActuarialValuation
