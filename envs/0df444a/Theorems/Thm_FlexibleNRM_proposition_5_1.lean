-- Prove2me | Theorems.Thm_FlexibleNRM_proposition_5_1
-- name    : FlexibleNRM.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:26:04.723235+00:00
-- url     : https://prove2.me/theorems/f893c68d-4699-4a41-a7f4-5659407d4df7
-- title:
--   Proposition 5.1 — $(1+\theta L)\sum_j\sum_{p\in\mathcal R_j}\hat\gamma_{jp1}\ge Z^*_{\mathrm{LP}}$
-- statement:
--   Assume substitutability, let $\theta\ge1$, and let $(\hat\gamma,\hat p,\hat S)$ be an output of the algorithm (4)–(6). Then
--   $$(1+\theta L)\sum_{j\in\mathcal J}\sum_{p\in\mathcal R_j}\hat\gamma_{jp1}\ge Z^*_{\mathrm{LP}}.$$
--   This is the first of the two steps of the performance guarantee: the calibrated parameters control the benchmark.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: (γ̂, p̂, Ŝ) computed by the algorithm (4)–(6) → the relation IsCalibration, with γ̂ total in p; reason: every output of the algorithm, for every tie-break in the two arg max, satisfies it and conversely; values at p ∉ R_j are never read
--   - encoding: the max of linear program (8) → zLP is the sSup of the objective values, with h and y total functions; reason: the milestone lp_feasible_bounded states that the sup is attained; the extra values of h and y are never read
--   - encoding: L = max_{j ∈ J, p ∈ R_j} |A_p| → maxResources N, a Finset.sup in ℕ, which is 0 when there are no products; reason: for n > 0 it is the paper's maximum (R_j, A_p nonempty); n = 0, where the paper's max is undefined, is a degenerate extra instance in which both sides are 0
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Proposition 5.1, p.14

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable
import Definitions.Def_FlexibleNRM_maxResources
import Definitions.Def_FlexibleNRM_IsCalibration
import Definitions.Def_FlexibleNRM_zLP

namespace FlexibleNRM

/-- **Proposition 5.1 (Optimal Performance Benchmark).** With `γ̂` computed through (4)–(6),
`(1 + θL) ∑_j ∑_{p ∈ R_j} γ̂_jp1 ≥ Z*_LP`.

Zhu, Topaloglu, manuscript of November 16, 2022, Proposition 5.1, p.14. -/
theorem proposition_5_1 {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N)
    {θ : ℝ} (hθ : 1 ≤ θ) {γ : Fin n → Fin r → ℕ → ℝ} {phat : Fin n → ℕ → Fin r}
    {Shat : ℕ → Finset (Fin n)} (hcal : IsCalibration N θ γ phat Shat) :
    zLP N ≤ (1 + θ * (maxResources N : ℝ)) * ∑ j, ∑ p ∈ N.R j, γ j p 1 := by sorry

end FlexibleNRM
