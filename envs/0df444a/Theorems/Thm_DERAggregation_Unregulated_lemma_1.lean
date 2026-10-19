-- Prove2me | Theorems.Thm_DERAggregation_Unregulated_lemma_1
-- name    : DERAggregation.Unregulated.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:59.008964+00:00
-- url     : https://prove2.me/theorems/2cdbffa5-6037-4e45-ac5c-7bb2a915d5a9
-- title:
--   Lemma 1, p. 5 — the prosumer's problem (1) has a unique optimum, with marginal utility of consumption equal to the price
-- statement:
--   Let $u$ be a prosumer's utility of consumption, $C$ her DER capacity and $Z$ the consumption bound, satisfying Assumption 1. Given a wholesale price $\lambda\in\mathbb R$, consider the prosumer's problem (1)
--   $$\max_{z}\ \lambda z+u(C-z)\quad\text{s.t.}\quad C-Z\le z\le C .$$
--   Then (1) has a unique optimal solution $z^*$. If moreover $\lambda>0$, it satisfies the first-order condition (2):
--   $$u'(C-z^*)=\lambda .$$
--
--   The lemma says that a price-taking prosumer consumes exactly up to the point where her marginal utility equals the wholesale price; it is the prosumer half of the competitive-equilibrium characterization of the benchmark dispatch.
--
--   **Formalization Note** The paper states (2) "given any $\lambda^k$". Under Assumption 1, $u'>0$ on $(0,Z)$, so (2) has no solution when $\lambda\le0$; the first-order condition is therefore stated for $\lambda>0$, while existence and uniqueness are stated for every $\lambda$.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 5, Lemma 1, (1), (2)

import Mathlib
import Definitions.Def_DERAggregation_Unregulated_Setting

namespace DERAggregation.Unregulated

open Set

/-- Lemma 1 (p. 5). Under Assumption 1, for every wholesale price `λ` the prosumer's problem (1)
has a unique optimal solution `z*`; when `λ > 0` it satisfies (2): `u'(C − z*) = λ`. -/
theorem lemma_1 (u : ℝ → ℝ) (C Z : ℝ) (hu : UtilAssm u C Z) (lam : ℝ) :
    (∃! z, IsOptPros u C Z lam z) ∧
      (0 < lam → ∀ z, IsOptPros u C Z lam z → deriv u (C - z) = lam) := by sorry

end DERAggregation.Unregulated
