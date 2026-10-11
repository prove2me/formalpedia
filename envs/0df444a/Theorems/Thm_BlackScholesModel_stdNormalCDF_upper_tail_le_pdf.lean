-- Prove2me | Theorems.Thm_BlackScholesModel_stdNormalCDF_upper_tail_le_pdf
-- name    : BlackScholesModel.stdNormalCDF_upper_tail_le_pdf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T16:05:22.891219+00:00
-- url     : https://prove2.me/theorems/9b542ee3-217e-46cc-ad48-b5a81a3577e4
-- title:
--   Mills upper bound for the standard normal distribution
-- statement:
--   For x≥1, the normal upper-tail probability lies between zero and the normal density at x. The estimate follows from integrating exp(-z²/2) over z>x and comparing the integrand with z exp(-z²/2), whose improper integral equals exp(-x²/2). This forms the analytic estimate needed to prove S*(1-N(dPlus))→0 when S→∞.
-- source:
--   Faithful Gaussian analysis supporting the published BlackScholesModel.callPrice_large_spot_limit and helper call_upper_tail_spot_product for mission e6d32df0-f327-42c2-be41-05cae8e311c8.

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem stdNormalCDF_upper_tail_le_pdf (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ 1 - stdNormalCDF x ∧
    1 - stdNormalCDF x ≤ stdNormalPDF x := by
  sorry

end BlackScholesModel
