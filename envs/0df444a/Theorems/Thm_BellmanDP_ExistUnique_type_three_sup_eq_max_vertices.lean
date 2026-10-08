-- Prove2me | Theorems.Thm_BellmanDP_ExistUnique_type_three_sup_eq_max_vertices
-- name    : BellmanDP.ExistUnique.type_three_sup_eq_max_vertices
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T15:45:41.694987+00:00
-- url     : https://prove2.me/theorems/02cd7a6a-7cd5-476e-b6f1-5d824df37554
-- title:
--   Chapter IV, Lemma 2 — two bounded solutions of the third-type equation differ most at a vertex
-- statement:
--   Assume the setting of Chapter IV, § 8: $n+1$ states, $M \ge 1$ transformations $T_l$ of the probability simplex $\Delta$ into itself with $p_{0l} \ne 1$ and $\sum_{k=1}^n p_{kl} \le c_1$ for a constant $0 < c_1 < 1$. Let $f$ and $g$ be two bounded solutions on $\Delta$ of
--   $$f(p) = \min\Big[\,1 + \sum_{k=0}^{n} p_k f(x_k),\ \min_{l}\big[1 + f(T_l p)\big]\Big] \quad (p \ne x_0), \qquad f(x_0) = 0.$$
--   Then
--   $$\sup_{p \in \Delta} |f(p) - g(p)| = \max_{0 \le k \le n} |f(x_k) - g(x_k)|.$$
--
--   This lemma is the first step of the uniqueness proof for Theorem 5: it reduces the comparison of two solutions to their values at the $n+1$ vertices of the simplex.
--
--   **Formalization Note** The equality of the supremum with the maximum is stated with `IsLUB` over the image of the simplex, which also asserts that the supremum exists.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter IV, § 8, Eqs. (8.1)-(8.2), p. 125, and Lemma 2, p. 127

import Mathlib
import Definitions.Def_BellmanDP_ExistUnique_TypeThree

namespace BellmanDP.ExistUnique

/-- Bellman, *Dynamic Programming*, Ch. IV, § 8, Lemma 2, p. 127. Under the hypotheses of
Theorem 5, for any two bounded solutions `f`, `g` of (8.1),
`Sup_p |f(p) − g(p)| = Max_k |f(x_k) − g(x_k)|`, the supremum over the simplex. -/
theorem type_three_sup_eq_max_vertices (n M : ℕ)
    (Tr : Fin M → (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ)) (c₁ : ℝ)
    (hT : TypeThreeHyp n M Tr c₁) (f g : (Fin (n + 1) → ℝ) → ℝ)
    (hf_bdd : BoundedOnSimplex n f) (hf : SolvesTypeThree n M Tr f)
    (hg_bdd : BoundedOnSimplex n g) (hg : SolvesTypeThree n M Tr g) :
    IsLUB ((fun p => |f p - g p|) '' simplex n)
      (⨆ k : Fin (n + 1), |f (vertex n k) - g (vertex n k)|) := by sorry

end BellmanDP.ExistUnique
