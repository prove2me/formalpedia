-- Prove2me | Theorems.Thm_ActuarialValuation_exposureCredibilityScaledRisk_square
-- name    : ActuarialValuation.exposureCredibilityScaledRisk_square
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T18:19:19.91419+00:00
-- url     : https://prove2.me/theorems/af356899-057a-4dfb-98ec-977c392941a9
-- title:
--   Scaled quadratic risk admits exact completing-square identity
-- statement:
--   This is an original derived actuarial theorem, based on the bühlmann–straub credibility using aggregate exposure and structural variance components. Completing the square shows why the Bühlmann–Straub exposure weight globally minimizes the quadratic credibility error. All financial amounts, exposure conditions and finite boundaries are given precisely by the Lean declaration; the result is not an assertion that this specific Lean statement has already been proved in the source.
--
--   Mathematical statement:
--
--   $$
--   Q_P(z)=(P\,\mathrm{VHM}+\mathrm{EPV})(z-Z(P))^2+\frac{P\,\mathrm{VHM}\,\mathrm{EPV}}{P\,\mathrm{VHM}+\mathrm{EPV}}
--   $$
-- source:
--   Original derived actuarial formalisation; S. David Promislow (2015), Fundamentals of Actuarial Mathematics, 3rd ed., printed page 489 (https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/). Parent framework: Loss Data Analytics, Chapter 12.2 / Bühlmann–Straub exposure weighting, supporting source https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The Lean declaration ActuarialValuation.exposureCredibilityScaledRisk_square is an original derived finite or algebraic specialisation, not a verbatim numbered published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_exposureCredibilityWeight
import Definitions.Def_actuarial_exposureCredibilityScaledRisk

namespace ActuarialValuation

theorem exposureCredibilityScaledRisk_square
  (EPV VHM P z : ℝ)
  (hE : 0 < EPV) (hV : 0 ≤ VHM) (hP : 0 ≤ P) :
  exposureCredibilityScaledRisk EPV VHM P z =
    (P * VHM + EPV) *
      (z - exposureCredibilityWeight EPV VHM P) ^ 2 +
    P * VHM * EPV / (P * VHM + EPV) := by sorry

end ActuarialValuation
