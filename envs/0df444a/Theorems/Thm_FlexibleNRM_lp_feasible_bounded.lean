-- Prove2me | Theorems.Thm_FlexibleNRM_lp_feasible_bounded
-- name    : FlexibleNRM.lp_feasible_bounded
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:25:36.272298+00:00
-- url     : https://prove2.me/theorems/21e3f4d8-8c1c-4acf-b74c-0c313bc143ab
-- title:
--   §5, p.13 — problem (8) is feasible and bounded, and attains its maximum
-- statement:
--   The linear program (8) is feasible and bounded, and $Z^*_{\mathrm{LP}}$ is the value of a feasible solution: the set of objective values of feasible solutions has greatest element $Z^*_{\mathrm{LP}}$.
--
--   This shows that $Z^*_{\mathrm{LP}}$ is a genuine optimal value, and it is the hypothesis of the strong duality step that leads to (10).
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: the max of linear program (8) → zLP is the sSup of the objective values, with h and y total functions; reason: the milestone lp_feasible_bounded states that the sup is attained; the extra values of h and y are never read
--   - reading: Problem (8) is feasible and bounded → IsGreatest: feasible, bounded and attained; reason: (8) is printed with max, and a feasible bounded linear program attains its optimum
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, §5, p.13

import Mathlib
import Definitions.Def_FlexibleNRM_zLP

namespace FlexibleNRM

/-- **Problem (8) is feasible and bounded**, and its maximum `Z*_LP` is attained.

Zhu, Topaloglu, manuscript of November 16, 2022, §5, p.13.

**Formalization Note** Attainment is what the `max` printed in (8) asserts. It says that the `sSup`
in `zLP` is not a junk value. -/
theorem lp_feasible_bounded {n m r : ℕ} (N : Network n m r) :
    IsGreatest (lpValues N) (zLP N) := by sorry

end FlexibleNRM
