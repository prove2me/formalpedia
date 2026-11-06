-- Prove2me | Theorems.Thm_FlexibleNRM_lemma_5_2
-- name    : FlexibleNRM.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:26:00.437196+00:00
-- url     : https://prove2.me/theorems/dd7ba92e-6976-4e8b-b423-a55e0ad05d01
-- title:
--   Lemma 5.2 — the opportunity cost of a route is bounded independently of $w$
-- statement:
--   Assume substitutability, let $\theta\ge1$, and let $(\hat\gamma,\hat p,\hat S)$ be an output of the algorithm (4)–(6). For every period $t$, route $p$ and $w\in\mathbb Z_+^{|\mathcal L|}$,
--   $$\hat\Psi_t(w)-\hat\Psi_t\Big(w-\sum_{i\in A_p}e_i\Big)\le\sum_{i\in A_p}\frac1{c_i}\sum_{k\in\mathcal J}\sum_{q\in\mathcal R_k}a_{iq}\,\hat\gamma_{kqt},$$
--   where $e_i$ is the $i$-th unit vector of $\mathbb Z^{|\mathcal L|}$. The right side is the state-independent opportunity cost that the algorithm subtracts in (4)–(6).
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: (γ̂, p̂, Ŝ) computed by the algorithm (4)–(6) → the relation IsCalibration, with γ̂ total in p; reason: every output of the algorithm, for every tie-break in the two arg max, satisfies it and conversely; values at p ∉ R_j are never read
--   - encoding: w ∈ Z₊ with w − Σ_{i∈A_p} e_i possibly negative → psi takes an integer vector w : Fin m → ℤ; reason: the source evaluates ψ_p at integer vectors; truncated subtraction would change the value
--   - generalization: t is a period of the horizon → t ∈ {1, …, T + 1}; reason: the proof of Proposition 5.4 applies the lemma at t + 1 ≤ T + 1, and periods of the horizon are included
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Lemma 5.2, p.15

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable
import Definitions.Def_FlexibleNRM_vfaResource
import Definitions.Def_FlexibleNRM_IsCalibration

namespace FlexibleNRM

/-- **Lemma 5.2 (Opportunity Cost).** For calibrated `γ̂` and any `w ∈ Z₊`,
`Ψ̂_t(w) − Ψ̂_t(w − ∑_{i ∈ A_p} e_i) ≤ ∑_{i ∈ A_p} (1 / c_i) ∑_k ∑_{q ∈ R_k} a_iq γ̂_kqt`.

Zhu, Topaloglu, manuscript of November 16, 2022, Lemma 5.2, p.15.

**Formalization Note** `t` ranges up to `T + 1`, since the proof of Proposition 5.4 applies the lemma
at `t + 1`. The vector `w − ∑_{i ∈ A_p} e_i` is integer valued, and a component can be `−1`. -/
theorem lemma_5_2 {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N)
    {θ : ℝ} (hθ : 1 ≤ θ) {γ : Fin n → Fin r → ℕ → ℝ} {phat : Fin n → ℕ → Fin r}
    {Shat : ℕ → Finset (Fin n)} (hcal : IsCalibration N θ γ phat Shat)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 (N.T + 1)) (p : Fin r) (w : Fin m → ℤ) (hw : 0 ≤ w) :
    vfaResource N γ t w - vfaResource N γ t (w - ∑ i ∈ N.A p, Pi.single i 1) ≤
      opportunityCost N γ p t := by sorry

end FlexibleNRM
