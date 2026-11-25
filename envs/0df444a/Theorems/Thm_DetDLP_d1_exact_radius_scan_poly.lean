-- Prove2me | Theorems.Thm_DetDLP_d1_exact_radius_scan_poly
-- name    : DetDLP.d1_exact_radius_scan_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:31:32.443741+00:00
-- url     : https://prove2.me/theorems/e86ef836-7790-4b4c-a1db-d5d9e16b4789
-- title:
--   Polynomial-time exact evaluation of the Appendix D radius
-- statement:
--   For every scale at least two and every degree bound, the integer scan computes exactly the floored base-two logarithm in Lemma 5.2, including both the ceiling in the degree cutoff and the lower bound of one. As a function of the two binary inputs the scan is polynomial-time.

import Definitions.Def_DetDLP_D1Radius
import Definitions.Def_DetDLP_W5_M6Sort
open DetDLP.D1

theorem DetDLP.d1_exact_radius_scan_poly : (∀ b deg : ℕ, 2 ≤ b → radiusScan (b,deg) = radius b deg) ∧ Groundwork.PolyT radiusScan := by sorry
