-- Prove2me | Theorems.Thm_FlexibleNRM_gamma_antitone
-- name    : FlexibleNRM.gamma_antitone
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:25:56.797375+00:00
-- url     : https://prove2.me/theorems/44a231a8-d21e-43f2-a18b-d5f01dd8f160
-- title:
--   Proof of Proposition 5.1, p.14 — the calibrated parameters are nonnegative and decreasing in $t$
-- statement:
--   Assume substitutability, let $\theta\ge1$, and let $(\hat\gamma,\hat p,\hat S)$ be an output of the algorithm (4)–(6). For every product $j$ and route $p\in\mathcal R_j$,
--   $$\hat\gamma_{jp1}\ge\hat\gamma_{jp2}\ge\dots\ge\hat\gamma_{jpT}\ge\hat\gamma_{jp,T+1}=0.$$
--   In particular $\hat\gamma_{jpt}\ge0$ for $t=1,\dots,T+1$. Both Proposition 5.1 and Lemma 5.2 rest on this sign.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: (γ̂, p̂, Ŝ) computed by the algorithm (4)–(6) → the relation IsCalibration, with γ̂ total in p; reason: every output of the algorithm, for every tie-break in the two arg max, satisfies it and conversely; values at p ∉ R_j are never read
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, proof of Proposition 5.1, p.14

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable
import Definitions.Def_FlexibleNRM_IsCalibration

namespace FlexibleNRM

/-- **The calibrated parameters are decreasing in `t` and nonnegative**:
`γ̂_jp1 ≥ γ̂_jp2 ≥ … ≥ γ̂_jpT ≥ γ̂_jp,T+1 = 0` for `p ∈ R_j`.

Zhu, Topaloglu, manuscript of November 16, 2022, proof of Proposition 5.1, p.14. -/
theorem gamma_antitone {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N)
    {θ : ℝ} (hθ : 1 ≤ θ) {γ : Fin n → Fin r → ℕ → ℝ} {phat : Fin n → ℕ → Fin r}
    {Shat : ℕ → Finset (Fin n)} (hcal : IsCalibration N θ γ phat Shat)
    (j : Fin n) (p : Fin r) (hp : p ∈ N.R j) :
    (∀ t ∈ Finset.Icc 1 N.T, γ j p (t + 1) ≤ γ j p t) ∧ γ j p (N.T + 1) = 0 ∧
      ∀ t ∈ Finset.Icc 1 (N.T + 1), 0 ≤ γ j p t := by sorry

end FlexibleNRM
