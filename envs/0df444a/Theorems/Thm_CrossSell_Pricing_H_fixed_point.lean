-- Prove2me | Theorems.Thm_CrossSell_Pricing_H_fixed_point
-- name    : CrossSell.Pricing.H_fixed_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:29:12.862556+00:00
-- url     : https://prove2.me/theorems/f168f557-5a5a-495a-a385-436853a6a9f8
-- title:
--   Theorem 1(b), p. 12 — H(z) = sup_r H(r; z) is finite and has a unique fixed point; strictly decreasing (added hypothesis S ≠ ∅)
-- statement:
--   Consider the sequential multinomial logit model with main offer set $S$, secondary sets $T_i$ ($i \in S^+ = S \cup \{0\}$), utilities $u_i, v_{il}$ and costs $c_i, s_l$, and finitely many secondary products. For a secondary price vector $\mathbf r$ and $z \in \mathbb R$ let
--   $$H(\mathbf r; z) = \sum_{i\in S}\exp\big((u_i - c_i - 1 - z) + t_i(\mathbf r)\big) + t_0(\mathbf r), \qquad t_i(\mathbf r) = \sum_{l\in T_i}\frac{(r_l - s_l)\exp(v_{il} - r_l)}{1 + \sum_{k\in T_i}\exp(v_{ik} - r_k)},$$
--   and $H(z) = \sup_{\mathbf r} H(\mathbf r; z)$. Then:
--
--   1. for every $z$, the set $\{H(\mathbf r; z) : \mathbf r\}$ is bounded above, so $H(z)$ is a finite real number;
--   2. the equation $z = H(z)$ has exactly one real solution;
--   3. if $S \neq \emptyset$, then $H$ is strictly decreasing in $z$.
--
--   This is the fixed-point part of Theorem 1(b) together with the theorem's final sentence. The unique fixed point is the quantity that Theorem 1(b) identifies with the optimal total profit; its existence and uniqueness make the scalar search (e.g. bisection) the paper describes well defined.
--
--   **Formalization Note.** The paper's $\max_{\mathbf r}$ is a real supremum here, and clause 1 asserts its finiteness. Clause 3 carries the hypothesis $S \neq \emptyset$, which the page does not state: for $S = \emptyset$, $H(z) = \sup_{\mathbf r} t_0(\mathbf r)$ is constant in $z$, so the printed claim fails in that degenerate case. Clauses 1 and 2 hold for every $S$, including $S = \emptyset$.
-- source:
--   Ke & Wang, Cross-Category Retailing Management: Substitution and Complementarity, accepted manuscript (SSRN 3383023), p. 12, Theorem 1(b) and its last sentence

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing

theorem H_fixed_point {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) :
    (∀ z : ℝ, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z)) ∧
    (∃! z : ℝ, z = Hmax S T u c s v z) ∧
    (S.Nonempty → StrictAnti (Hmax S T u c s v)) := by sorry

end CrossSell.Pricing
