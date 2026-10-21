-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_kl_projection_exists_unique
-- name    : CloudMWU.Bicriteria.kl_projection_exists_unique
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:19.363204+00:00
-- url     : https://prove2.me/theorems/364e3d89-99ad-49b7-9491-3a54bdd87907
-- title:
--   Appendix A, problem (Q), p. 25 — the KL projection onto Δ_ε exists and is unique; every h_1 ∈ Δ_ε starts exactly one run of Algorithm 1
-- statement:
--   Let $N \ge 2$ and $0 < \varepsilon \le 1/10$, and let $\Delta_\varepsilon = \{x \in \mathbb R^N : \sum_i x(i) = 1,\ x(i) \ge \varepsilon/N\}$.
--
--   1. For every $y \in \mathbb R^N$ with $y(i) > 0$ for all $i$, the convex problem
--   $$(Q) \qquad \min_{x \in \Delta_\varepsilon} \ \sum_i x(i) \ln\frac{x(i)}{y(i)}$$
--   has exactly one minimizer, so the KL projection $\pi_{\Delta_\varepsilon}(y)$ is well defined.
--   2. Consequently, for every $\eta$, every SLA vector $\beta$, every load sequence $L$ and every starting allocation $h_1 \in \Delta_\varepsilon$, there is exactly one run of Algorithm 1 that starts at $h_1$.
--
--   The paper takes the projection for granted. This statement makes sure that the predicate "is a run of Algorithm 1", on which every other result of the mission is stated, is satisfied by exactly one sequence for each start, so that none of those results is vacuous.
--
--   **Formalization Note** The positivity of $y$ is added: $\ln(x(i)/y(i))$ needs it, and in a run the vector being projected, $\widehat h_{t+1}(i) = h_t(i)e^{\eta g_t(i)}$, is always positive. Part 2 places no condition on $\eta$, $\beta$ or $L$.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 25, Appendix A, proof of Proposition 1, problem (Q); p. 9, Algorithm 1 (line 1: h_1 any allocation over Δ_ε)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem kl_projection_exists_unique (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10) :
    (∀ y : Fin N → ℝ, (∀ i, 0 < y i) → ∃! x : Fin N → ℝ, IsKLProj ε y x) ∧
    (∀ (η : ℝ) (β : Fin N → ℝ) (L : ℕ → Fin N → ℝ) (h₀ : Fin N → ℝ), h₀ ∈ truncSimplex N ε →
      ∃! h : ℕ → Fin N → ℝ, h 0 = h₀ ∧ IsAlg1Run ε η β L h) := by sorry

end CloudMWU.Bicriteria
