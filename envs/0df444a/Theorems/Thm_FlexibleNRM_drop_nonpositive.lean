-- Prove2me | Theorems.Thm_FlexibleNRM_drop_nonpositive
-- name    : FlexibleNRM.drop_nonpositive
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:25:43.282251+00:00
-- url     : https://prove2.me/theorems/9832a13f-938d-4578-800c-e7c92a802165
-- title:
--   §2, p.8 — dropping products of non-positive net contribution preserves optimality
-- statement:
--   Assume substitutability. Let $t$ be a period, $b\in\mathbb R^{\mathcal J}$ a vector of net contributions, $S\subseteq\mathcal J$ an assortment, and $S'=\{j\in S: b_j>0\}$. Then:
--
--   1. $\sum_j\phi_{jt}(S)\,b_j^+\le\sum_j\phi_{jt}(S')\,b_j$;
--   2. if $S$ maximizes $Q\mapsto\sum_j\phi_{jt}(Q)\,b_j$, then so does $S'$;
--   3. if $S$ maximizes it, then $\phi_{jt}(S)\,b_j\ge0$ for every $j$.
--
--   The paper uses this step three times: after (2), for (5) in the proof of Proposition 5.1, and for (7) in the proof of Proposition 5.4.
--
--   Differences from the source:
--   - encoding: finite sets of products, resources and routes; c_i, R_j, A_p used as nondegenerate → Fin n, Fin m, Fin r; fields 0 < c i, (R j).Nonempty, (A p).Nonempty; routes are one type with R : Fin n → Finset (Fin r); reason: same instances; the three conditions only exclude expressions the source leaves undefined (division by c_i, arg max over R_j, min over A_p)
--   - encoding: implicit: φ_jt(S) ≥ 0, Σ_j φ_jt(S) ≤ 1, a customer chooses within the offered assortment (pp.2, 7) → the published PersonalizedAssortment.IB.ChoiceModel, one per period; reason: the fields are exactly these conditions; values outside the periods are never read
--   - generalization: f_j is the revenue of product j → f j is any real number; reason: the source never uses a sign of f_j; nonnegative revenues are an instance
--   - generalization: the sentence is about b_j = 1(F(x+e_j)≠∅)(f_j + J_{t+1}(x+e_j) − J_{t+1}(x)) and concludes that the reduced solution is optimal → any b; clause (ii) is that conclusion, and clauses (i) and (iii) are added; reason: the paper reuses the reasoning for (5) and (7); (i) is what the argument shows, and (iii) replaces the claim Δ_jt ≥ 0 for j ∈ Ŝ_t of p.14, which fails for a product of zero choice probability
-- source:
--   Zhu, Topaloglu, Performance Guarantees for Network Revenue Management with Flexible Products, manuscript of November 16, 2022, §2, after Eq. (2), p.8

import Mathlib
import Definitions.Def_FlexibleNRM_Substitutable

namespace FlexibleNRM

/-- **Dropping products with non-positive net contribution (the substitutability step).**
Let `b` be any vector of net contributions, `t` a period and `S'` the set of `j ∈ S` with `b j > 0`.
Then (i) `∑_j φ_jt(S) b_j⁺ ≤ ∑_j φ_jt(S') b_j`, and if `S` maximizes `∑_j φ_jt(S) b_j`, then
(ii) so does `S'`, and (iii) `φ_jt(S) b_j ≥ 0` for every `j`.

Zhu, Topaloglu, manuscript of November 16, 2022, §2, after Eq. (2), p.8.

**Formalization Note** The sentence on p.8 is about `b_j = 1(F(x + e_j) ≠ ∅) (f_j + J_{t+1}(x + e_j)
− J_{t+1}(x))`. It is stated for arbitrary `b`, because the paper reuses the same reasoning for (5)
on p.14 and for (7) on pp.11 and 17. Clause (iii) replaces the paper's "`∆_jt ≥ 0` for `j ∈ Ŝ_t`",
which fails for products of zero choice probability. -/
theorem drop_nonpositive {n m r : ℕ} (N : Network n m r) (hsub : Substitutable N)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 N.T) (b : Fin n → ℝ) (S : Finset (Fin n)) :
    (∑ j, (N.φ t).prob S j * max (b j) 0 ≤
      ∑ j, (N.φ t).prob (S.filter fun k => 0 < b k) j * b j) ∧
    ((∀ Q : Finset (Fin n), ∑ j, (N.φ t).prob Q j * b j ≤ ∑ j, (N.φ t).prob S j * b j) →
      (∀ Q : Finset (Fin n), ∑ j, (N.φ t).prob Q j * b j ≤
        ∑ j, (N.φ t).prob (S.filter fun k => 0 < b k) j * b j) ∧
      ∀ j, 0 ≤ (N.φ t).prob S j * b j) := by sorry

end FlexibleNRM
