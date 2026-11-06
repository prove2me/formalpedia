-- Prove2me | Theorems.Thm_FlexibleNRM_eq_10
-- name    : FlexibleNRM.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:25:53.800702+00:00
-- url     : https://prove2.me/theorems/175375a2-27ef-47a0-84ef-c94fa3a0d042
-- title:
--   Eq. (10) — $Z^*_{\mathrm{LP}}$ equals the minimum of the dual form in $\mu$
-- statement:
--   The optimal value of (8) is given by
--   $$Z^*_{\mathrm{LP}}=\min_{\mu\in\mathbb R^{|\mathcal L|}_+}\Big\{\sum_{t\in\mathcal T}\max_{S\subseteq\mathcal J}\Big\{\sum_{j\in\mathcal J}\phi_{jt}(S)\max_{p\in\mathcal R_j}\Big\{f_j-\sum_{i\in\mathcal L}a_{ip}\mu_i\Big\}\Big\}+\sum_{i\in\mathcal L}c_i\mu_i\Big\},$$
--   and the minimum is attained. Proposition 5.1 evaluates this objective at a dual solution built from the calibrated parameters.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: the max of linear program (8) → zLP is the sSup of the objective values, with h and y total functions; reason: the milestone lp_feasible_bounded states that the sup is attained; the extra values of h and y are never read
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Eq. (10), p.14

import Mathlib
import Definitions.Def_FlexibleNRM_zLP
import Definitions.Def_FlexibleNRM_dualObjective

namespace FlexibleNRM

/-- **Eq. (10).** `Z*_LP = min_{μ ≥ 0} { ∑_t max_{S ⊆ J} { ∑_j φ_jt(S) max_{p ∈ R_j}
{ f_j − ∑_i a_ip μ_i } } + ∑_i c_i μ_i }`.

Zhu, Topaloglu, manuscript of November 16, 2022, Eq. (10), p.14. -/
theorem eq_10 {n m r : ℕ} (N : Network n m r) :
    IsLeast {v : ℝ | ∃ μ : Fin m → ℝ, 0 ≤ μ ∧ v = dualObjective N μ} (zLP N) := by sorry

end FlexibleNRM
