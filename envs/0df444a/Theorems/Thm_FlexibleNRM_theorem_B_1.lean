-- Prove2me | Theorems.Thm_FlexibleNRM_theorem_B_1
-- name    : FlexibleNRM.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:27:40.954759+00:00
-- url     : https://prove2.me/theorems/4b9b8d2a-92ab-44ea-b866-5babac2b221b
-- title:
--   Theorem B.1 — the linear program bounds the optimal revenue, $Z^*_{\mathrm{LP}}\ge J_1(0)$
-- statement:
--   Assume substitutability. The optimal value of the linear program (8) is at least the optimal total expected revenue:
--   $$Z^*_{\mathrm{LP}}\ge J_1(0).$$
--   This is the upper bound against which the approximate policy is measured.
--
--   **Formalization Note** Substitutability is what yields an optimal policy that does not offer unavailable products, and the feasibility of its expected decisions in (8) relies on that.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - reading: Eq. (2), whose first line is misprinted → optValue follows the second line of (2); reason: the source says the second line follows by rearranging, and uses only it
--   - encoding: the max of linear program (8) → zLP is the sSup of the objective values, with h and y total functions; reason: the milestone lp_feasible_bounded states that the sup is attained; the extra values of h and y are never read
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Theorem B.1, p.31

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable
import Definitions.Def_FlexibleNRM_optValue
import Definitions.Def_FlexibleNRM_zLP

namespace FlexibleNRM

/-- **Theorem B.1.** `Z*_LP ≥ J_1(0)`.

Zhu, Topaloglu, manuscript of November 16, 2022, Theorem B.1, p.31.

**Formalization Note** Substitutability stays a hypothesis: the proof uses an optimal policy that
offers no unavailable product, and p.8 obtains such a policy from substitutability. -/
theorem theorem_B_1 {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N) :
    optValue N 1 0 ≤ zLP N := by sorry

end FlexibleNRM
