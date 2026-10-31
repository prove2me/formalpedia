-- Prove2me | Theorems.Thm_FBMSP_singlePrice_attains
-- name    : FBMSP.singlePrice_attains
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:53:56.885774+00:00
-- url     : https://prove2.me/theorems/8c67e76f-bc7d-4750-a4df-c21781df811b
-- title:
--   Section 2.2 — Attainment of the least monopoly price
-- statement:
--   For any integrable mean-zero error law and nonnegative predicted value $x$, the infimum defining $p_\epsilon(x)$ is an actual least revenue-maximizing nonnegative price, and
--   $$p_\epsilon(x)S(p_\epsilon(x)-x)=R_\epsilon(x).$$
--   This supplies the optimizer-existence obligation implicit in the source's notation. It does not assume that optimal prices are unique.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Section 2.2, p.11, definitions of price, margin, and revenue.

import Definitions.Def_FBMSP_Model

namespace FBMSP

/-- Supporting attainment obligation for the source's least-optimizer
definition of p_epsilon.  Draft statement; proof remains open. -/
theorem singlePrice_attains (η : MeasureTheory.Measure ℝ)
    (hnoise : ValidNoise η) (x : ℝ) (hx : 0 ≤ x) :
    IsLeastOptimalPrice η x (singlePrice η x) ∧
      postedRevenue η x (singlePrice η x) = singleRevenue η x := by sorry

end FBMSP
