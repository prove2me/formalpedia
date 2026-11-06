-- Prove2me | Theorems.Thm_FlexibleNRM_theorem_4_1
-- name    : FlexibleNRM.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:05.946403+00:00
-- url     : https://prove2.me/theorems/3a27dce6-31ff-461b-90a5-e475beb87e66
-- title:
--   Theorem 4.1 (Performance Guarantee) — the approximate policy earns at least a $1/(1+\theta L)$ fraction of the optimal revenue
-- statement:
--   Consider a network revenue management instance with flexible products whose choice probabilities are substitutable. Let $\theta\ge1$, let $(\hat\gamma,\hat p,\hat S)$ be an output of the calibration algorithm (4)–(6) with tuning parameter $\theta$, and let $S^{\mathrm{App}}$ be the greedy policy (7) with respect to the resulting value function approximations. With $L=\max_{j\in\mathcal J,\,p\in\mathcal R_j}|A_p|$,
--   $$U_1(0)\ge\frac1{1+\theta L}\,J_1(0).$$
--   That is, the total expected revenue obtained by the approximate policy is at least a $1/(1+\theta L)$ fraction of the optimal total expected revenue. Taking $\theta=1$ gives the factor $1/(1+L)$ of the abstract.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - reading: the total expected revenue obtained by the approximate policy, and the optimal total expected revenue → policyValue at period 1 in state 0, and optValue at period 1 in state 0; reason: the proof on p.18 identifies them as U_1(0) and J_1(0), the values of the dynamic programs (11) and (2)
--   - reading: Eq. (2), whose first line is misprinted → optValue follows the second line of (2); reason: the source says the second line follows by rearranging, and uses only it
--   - encoding: (γ̂, p̂, Ŝ) computed by the algorithm (4)–(6) → the relation IsCalibration, with γ̂ total in p; reason: every output of the algorithm, for every tie-break in the two arg max, satisfies it and conversely; values at p ∉ R_j are never read
--   - encoding: Ĵ_t(x) is a max over (y, w), Eq. (3) → vfa is the sSup of the attained values, with junk value 0 when F(x) = ∅; reason: the set of values is finite, so at feasible x the sSup is the max; the junk value is read only under the indicator of F(x + e_j) ≠ ∅, where it is multiplied by 0
--   - reading: Eq. (7) prints S_t^App(x) = max → S_t^App(x) is a maximizer; reason: the next sentence speaks of an optimal solution, and (11) evaluates φ_jt at S_t^App(x)
--   - generalization: S_t^App(x) is a maximizer of (7) with no unavailable product, and the proof assumes it offers no product of non-positive net contribution → IsApproxPolicy allows every maximizer of (7), and constrains only states with F(x) ≠ ∅; reason: the policy the source selects is one of these, and the policy never leaves the feasible states from x = 0
--   - encoding: L = max_{j ∈ J, p ∈ R_j} |A_p| → maxResources N, a Finset.sup in ℕ, which is 0 when there are no products; reason: for n > 0 it is the paper's maximum (R_j, A_p nonempty); n = 0, where the paper's max is undefined, is a degenerate extra instance in which both sides are 0
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Theorem 4.1, p.12

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable
import Definitions.Def_FlexibleNRM_maxResources
import Definitions.Def_FlexibleNRM_optValue
import Definitions.Def_FlexibleNRM_policyValue
import Definitions.Def_FlexibleNRM_IsCalibration
import Definitions.Def_FlexibleNRM_IsApproxPolicy

namespace FlexibleNRM

/-- **Theorem 4.1 (Performance Guarantee).** The total expected revenue obtained by the approximate
policy is at least `1 / (1 + θL)` fraction of the optimal total expected revenue:
`U_1(0) ≥ J_1(0) / (1 + θL)`.

Zhu, Topaloglu, manuscript of November 16, 2022, Theorem 4.1, p.12.

**Formalization Note** The two revenues are `U_1(0)` and `J_1(0)`, by the paper's identification in
the proof on p.18. The statement covers every instance, every `θ ≥ 1`, every output `(γ̂, p̂, Ŝ)` of
(4)–(6) and every maximizer of (7), so every tie-break is included. -/
theorem theorem_4_1 {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N)
    {θ : ℝ} (hθ : 1 ≤ θ) {γ : Fin n → Fin r → ℕ → ℝ} {phat : Fin n → ℕ → Fin r}
    {Shat : ℕ → Finset (Fin n)} (hcal : IsCalibration N θ γ phat Shat)
    {Sapp : ℕ → (Fin n → ℕ) → Finset (Fin n)} (hpol : IsApproxPolicy N γ Sapp) :
    (1 / (1 + θ * (maxResources N : ℝ))) * optValue N 1 0 ≤ policyValue N Sapp 1 0 := by sorry

end FlexibleNRM
