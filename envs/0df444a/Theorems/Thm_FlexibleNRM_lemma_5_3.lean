-- Prove2me | Theorems.Thm_FlexibleNRM_lemma_5_3
-- name    : FlexibleNRM.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:27:08.458543+00:00
-- url     : https://prove2.me/theorems/5537f2b4-3818-431a-bf7d-1d5e61ed4e45
-- title:
--   Lemma 5.3 — one more purchase stays feasible and bounds $\hat J_t(x+e_j)$ from below
-- statement:
--   Let $x\in\mathbb Z_+^{|\mathcal J|}$, $y\in\mathcal F(x)$, $j\in\mathcal J$ and $p\in\mathcal R_j$, and put $w_i=c_i-\sum_{k}\sum_{q\in\mathcal R_k}a_{iq}y_{kq}$ for all $i$. If $w_i\ge1$ for all $i\in A_p$, then
--   $$\mathcal F(x+e_j)\ne\emptyset\qquad\text{and}\qquad\hat J_t(x+e_j)\ge\hat\Psi_t\Big(w-\sum_{i\in A_p}e_i\Big).$$
--   A route with spare capacity on all its resources can take one more customer, and the assignment that does so is feasible in (3).
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - encoding: Ĵ_t(x) is a max over (y, w), Eq. (3) → vfa is the sSup of the attained values, with junk value 0 when F(x) = ∅; reason: the set of values is finite, so at feasible x the sSup is the max; the junk value is read only under the indicator of F(x + e_j) ≠ ∅, where it is multiplied by 0
--   - encoding: w ∈ Z₊ with w − Σ_{i∈A_p} e_i possibly negative → psi takes an integer vector w : Fin m → ℤ; reason: the source evaluates ψ_p at integer vectors; truncated subtraction would change the value
--   - generalization: the parameters γ̂ of the algorithm and a period t → arbitrary real parameters γ and any t : ℕ; reason: the proof uses neither the calibration nor the period, and the calibrated parameters are an instance
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, Lemma 5.3, p.15

import Mathlib
import Definitions.Def_FlexibleNRM_Feasible
import Definitions.Def_FlexibleNRM_vfa

namespace FlexibleNRM

/-- **Lemma 5.3 (Value Function Approximation Bound).** For any `x ∈ Z₊`, `y ∈ F(x)`, `j ∈ J` and
`p ∈ R_j`, letting `w_i = c_i − ∑_k ∑_{q ∈ R_k} a_iq y_kq` for all `i`, if `w_i ≥ 1` for all
`i ∈ A_p`, then `F(x + e_j) ≠ ∅` and `Ĵ_t(x + e_j) ≥ Ψ̂_t(w − ∑_{i ∈ A_p} e_i)`.

Zhu, Topaloglu, manuscript of November 16, 2022, Lemma 5.3, p.15.

**Formalization Note** The proof reads neither the calibration nor the period, so `γ` and `t` are
arbitrary. `w` is integer valued, so `c_i − …` is not truncated. -/
theorem lemma_5_3 {n m r : ℕ} (N : Network n m r) (γ : Fin n → Fin r → ℕ → ℝ) (t : ℕ)
    (x : Fin n → ℕ) (y : Fin n → Fin r → ℕ) (hy : y ∈ routeAssignments N x)
    (j : Fin n) (p : Fin r) (hp : p ∈ N.R j) (w : Fin m → ℤ)
    (hw : ∀ i, w i = (N.c i : ℤ) - ∑ k, ∑ q ∈ N.R k, (N.a i q : ℤ) * (y k q : ℤ))
    (hw1 : ∀ i ∈ N.A p, 1 ≤ w i) :
    Feasible N (x + Pi.single j 1) ∧
      vfaResource N γ t (w - ∑ i ∈ N.A p, Pi.single i 1) ≤
        vfa N γ t (x + Pi.single j 1) := by sorry

end FlexibleNRM
