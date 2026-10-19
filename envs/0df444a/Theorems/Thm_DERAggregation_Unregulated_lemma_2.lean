-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_lemma_2
-- name    : DERAggregation.Unregulated.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:59.50586+00:00
-- url     : https://prove2.me/theorems/6aeffa2a-c219-4874-9fbb-984c5fc536ec
-- title:
--   Lemma 2, p. 6 — the generator's problem (3) has a unique optimum, with marginal cost equal to the price
-- statement:
--   Let $c$ be a generator's cost function on $[\underline y,\overline y]$ satisfying Assumption 2. Given a wholesale price $\lambda\in\mathbb R$, consider the generator's problem (3)
--   $$\max_{y\in[\underline y,\overline y]}\ \lambda y-c(y).$$
--   Then (3) has a unique optimal solution $y^*$. If moreover $\lambda>0$, it satisfies the first-order condition (4):
--   $$c'(y^*)=\lambda .$$
--
--   This is the generator half of the competitive-equilibrium characterization: a price-taking generator produces where marginal cost equals the wholesale price.
--
--   **Formalization Note** The paper states (4) "given any $\lambda^k$". Under Assumption 2, $c'>0$ on the open interval, so (4) has no solution when $\lambda\le0$; the first-order condition is stated for $\lambda>0$, existence and uniqueness for every $\lambda$.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 6, Lemma 2, (3), (4)

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Lemma 2 (p. 6). Under Assumption 2, for every wholesale price `λ` the generator's problem (3)
has a unique optimal solution `y*`; when `λ > 0` it satisfies (4): `c'(y*) = λ`. -/
theorem lemma_2 (c : ℝ → ℝ) (lo hi : ℝ) (hc : CostAssm c lo hi) (lam : ℝ) :
    (∃! y, IsOptGen c lo hi lam y) ∧
      (0 < lam → ∀ y, IsOptGen c lo hi lam y → deriv c y = lam) := by sorry

end DERAggregation.Unregulated
