-- Prove2me | Theorems.Thm_FMLPricing_BranchBound_proposition_6
-- name    : FMLPricing.BranchBound.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:35:42.577014+00:00
-- url     : https://prove2.me/theorems/988abf12-3f5f-40fa-b7cf-dd0ebc67d2de
-- title:
--   Proposition 6, p. 15 — the derivative-free bound π^ξ(x, r) bounds π on R(x, r) ∩ X
-- statement:
--   Let $x \in X$ and $r > 0$, and let $R(x, r) = [\underline x(x, r), \bar x(x, r)]$ be the clipped box of radius $r$ around $x$. Then
--   $$
--   \pi(\tilde x) \le \pi^\xi(x, r) \quad \text{for every } \tilde x \in R(x, r) \cap X,
--   $$
--   where $\pi^\xi(x, r)$ is the optimal value of the concave relaxation
--   $$
--   \max_{\xi \in \mathbb R^{m \times n}} \; -\sum_{c \in M,\, j \in N} \xi_{cj} \log\!\Big(\frac{\xi_{cj}}{\bar x_c(x, r)}\Big) s_{cj} w_c b_j^{-1}
--   $$
--   subject to $\underline z_j \underline x_c(x, r) \le \xi_{cj} \le \bar z_j \bar x_c(x, r)$ and $1 - \bar x_c(x, r) \le \sum_j s_{cj} \xi_{cj} \le 1 - \underline x_c(x, r)$.
--
--   This is the derivative-free term of the paper's bounding rule $\pi^u$ (12). On its own it gives a valid upper bound over the box, but not the estimate $\pi^\xi(x, r) \le \pi(x) + r K'$ that the termination proof of Theorem 1 uses.
--
--   **Formalization Note** $\pi^\xi(x, r)$ is a real supremum. Its feasible set is compact, and it is nonempty whenever $R(x, r) \cap X \neq \emptyset$.
-- source:
--   van de Geer & den Boer, Price Optimization Under the Finite-Mixture Logit Model, SSRN 3235432 (version of August 26, 2021), p. 15, Proposition 6 (proof p. 42)

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model

namespace FMLPricing.BranchBound

/-- Proposition 6, p. 15: for `x ∈ X` and `r > 0`, `π` is bounded on `R(x, r) ∩ X` by the
derivative-free bound `π^ξ(x, r)`. -/
theorem proposition_6 {m n : ℕ} (I : FML m n) (hI : Standing I)
    (x : Fin m → ℝ) (hx : x ∈ Xset I) (r : ℝ) (hr : 0 < r) :
    ∀ x' ∈ Rbox I x r ∩ Xset I, piX I x' ≤ piXi I x r := by sorry

end FMLPricing.BranchBound
