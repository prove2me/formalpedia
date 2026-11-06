-- Prove2me | Theorems.Thm_FlexibleNRM_proposition_5_4
-- name    : FlexibleNRM.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:28:12.067027+00:00
-- url     : https://prove2.me/theorems/dadab281-64f1-4a0c-a612-4a70bcdf8f6c
-- title:
--   Proposition 5.4 — $U_t(x)\ge\hat J_t(x)$ at every feasible state
-- statement:
--   Assume substitutability, let $\theta\ge1$, let $(\hat\gamma,\hat p,\hat S)$ be an output of the algorithm (4)–(6), and let $S^{\mathrm{App}}$ be an approximate policy for $\hat\gamma$. For every $x\in\mathbb Z_+^{|\mathcal J|}$ with $\mathcal F(x)\ne\emptyset$ and every period $t$,
--   $$U_t(x)\ge\hat J_t(x).$$
--   This is the second of the two steps of the performance guarantee: the policy earns at least what the approximation promises.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: (γ̂, p̂, Ŝ) computed by the algorithm (4)–(6) → the relation IsCalibration, with γ̂ total in p; reason: every output of the algorithm, for every tie-break in the two arg max, satisfies it and conversely; values at p ∉ R_j are never read
--   - encoding: Ĵ_t(x) is a max over (y, w), Eq. (3) → vfa is the sSup of the attained values, with junk value 0 when F(x) = ∅; reason: the set of values is finite, so at feasible x the sSup is the max; the junk value is read only under the indicator of F(x + e_j) ≠ ∅, where it is multiplied by 0
--   - reading: Eq. (7) prints S_t^App(x) = max → S_t^App(x) is a maximizer; reason: the next sentence speaks of an optimal solution, and (11) evaluates φ_jt at S_t^App(x)
--   - generalization: S_t^App(x) is a maximizer of (7) with no unavailable product, and the proof assumes it offers no product of non-positive net contribution → IsApproxPolicy allows every maximizer of (7), and constrains only states with F(x) ≠ ∅; reason: the policy the source selects is one of these, and the policy never leaves the feasible states from x = 0
--   - generalization: t ∈ T → t ∈ {1, …, T + 1}; reason: the source's induction starts at T + 1, and the periods of the horizon are included
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Proposition 5.4, p.16

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable
import Definitions.Def_FlexibleNRM_IsCalibration
import Definitions.Def_FlexibleNRM_IsApproxPolicy
import Definitions.Def_FlexibleNRM_policyValue

namespace FlexibleNRM

/-- **Proposition 5.4 (Approximate Policy Performance Benchmark).** For any `x ∈ Z₊` with
`F(x) ≠ ∅` and `t ∈ T`, `U_t(x) ≥ Ĵ_t(x)`.

Zhu, Topaloglu, manuscript of November 16, 2022, Proposition 5.4, p.16.

**Formalization Note** `t` ranges up to `T + 1`, where the paper's induction starts. The inequality
holds for every maximizer of (7) and of (4), (5). -/
theorem proposition_5_4 {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N)
    {θ : ℝ} (hθ : 1 ≤ θ) {γ : Fin n → Fin r → ℕ → ℝ} {phat : Fin n → ℕ → Fin r}
    {Shat : ℕ → Finset (Fin n)} (hcal : IsCalibration N θ γ phat Shat)
    {Sapp : ℕ → (Fin n → ℕ) → Finset (Fin n)} (hpol : IsApproxPolicy N γ Sapp)
    (x : Fin n → ℕ) (hx : Feasible N x) (t : ℕ) (ht : t ∈ Finset.Icc 1 (N.T + 1)) :
    vfa N γ t x ≤ policyValue N Sapp t x := by sorry

end FlexibleNRM
