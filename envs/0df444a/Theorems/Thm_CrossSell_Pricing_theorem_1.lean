-- Prove2me | Theorems.Thm_CrossSell_Pricing_theorem_1
-- name    : CrossSell.Pricing.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:27.128143+00:00
-- url     : https://prove2.me/theorems/c6b12a9d-7cf4-44e3-9196-70d00f32563d
-- title:
--   Theorem 1, p. 12 — optimal prices equalize aggregate markups; the optimal profit is the unique fixed point of H(z) = sup_r H(r; z), strictly decreasing for S ≠ ∅
-- statement:
--   Consider the sequential multinomial logit model of cross-category retailing: a firm offers a finite set $S$ of main products, with $S^+ = S \cup \{0\}$; after the first-stage outcome $i \in S^+$ a consumer may buy one secondary product from $T_i$, chosen from finitely many secondary products. Main product $i$ has intrinsic utility $u_i$ and cost $c_i$; secondary product $l$ has cost $s_l$ and intrinsic utility $v_{il}$ after outcome $i$. With main prices $\mathbf p$ and secondary prices $\mathbf r$ the total expected profit is $\Pi(S,\mathbf T,\mathbf p,\mathbf r)$ of eq. (5), the secondary profit of $T_i$ is
--   $$t_i(\mathbf r) = \sum_{l\in T_i}\frac{(r_l - s_l)\exp(v_{il} - r_l)}{1 + \sum_{k\in T_i}\exp(v_{ik} - r_k)},$$
--   and
--   $$H(\mathbf r; z) = \sum_{i\in S}\exp\big((u_i - c_i - 1 - z) + t_i(\mathbf r)\big) + t_0(\mathbf r), \qquad H(z) = \sup_{\mathbf r} H(\mathbf r; z).$$
--   Then:
--
--   1. **(a)** at every joint maximizer $(\mathbf p, \mathbf r)$ of $\Pi$, the aggregate markup $p_i - c_i + t_i(\mathbf r)$ is the same for all $i \in S$;
--   2. for every $z$, $\{H(\mathbf r; z) : \mathbf r\}$ is bounded above, so $H(z)$ is finite;
--   3. **(b)** the equation $z = H(z)$ has exactly one solution $z^*$, and $z^*$ is the optimal total profit: the least upper bound of $\{\Pi(S,\mathbf T,\mathbf p,\mathbf r) : \mathbf p, \mathbf r\}$;
--   4. if $S \neq \emptyset$, $H(z)$ is strictly decreasing in $z$.
--
--   The theorem reduces the joint pricing problem, which has up to $M + N$ variables and is not concave, to a secondary-price problem $\max_{\mathbf r} H(\mathbf r; z)$ and a one-dimensional fixed-point search.
--
--   **Formalization Note.** "Optimality" is global maximization of $\Pi$ over all real price vectors with $S$ and $\mathbf T$ fixed. The optimal total profit is stated as the least upper bound of the profit values (the paper's "max" presumes attainment, which the page does not show; the companion milestone on the p. 13 price formula gives attainment whenever $H(\cdot; z^*)$ has a maximizer). $H(z)$ is a real supremum, made meaningful by clause 2. Clause 4 carries the hypothesis $S \neq \emptyset$, not printed on the page: for $S = \emptyset$, $H$ is constant, so strict decrease fails; the other clauses hold for every $S$.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 12, Theorem 1

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem theorem_1 {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) :
    (∀ (p : ι → ℝ) (r : κ → ℝ),
        (∀ (p' : ι → ℝ) (r' : κ → ℝ), profit S T u c s v p' r' ≤ profit S T u c s v p r) →
        ∀ i ∈ S, ∀ j ∈ S, aggMarkup T c s v p r i = aggMarkup T c s v p r j) ∧
    (∀ z : ℝ, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z)) ∧
    (∃ zstar : ℝ, zstar = Hmax S T u c s v zstar ∧
        (∀ z : ℝ, z = Hmax S T u c s v z → z = zstar) ∧
        IsLUB (Set.range fun pr : (ι → ℝ) × (κ → ℝ) => profit S T u c s v pr.1 pr.2) zstar) ∧
    (S.Nonempty → StrictAnti (Hmax S T u c s v)) := by sorry

end CrossSell.Pricing
