-- Prove2me | Theorems.Thm_CloudMWU_Bicriteria_proposition_1b
-- name    : CloudMWU.Bicriteria.proposition_1b
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:14.20785+00:00
-- url     : https://prove2.me/theorems/04816d38-43f9-423c-8163-16f1a9e948ee
-- title:
--   Proposition 1(b), p. 9 — π_{Δ_ε}(y)(i) = y(i)e^{μ_i}C with C = (1 − (ε/N)|S|)/Σ_{j∉S} y(j), μ_i ≥ 0, μ_i = 0 off S
-- statement:
--   Let $N \ge 2$, $0 < \varepsilon \le 1/10$, let $y \in \mathbb R^N$ with $y(i) > 0$ for all $i$, and let $x = \pi_{\Delta_\varepsilon}(y)$ be the KL projection of $y$ onto the truncated simplex. Let $S = \{i : x(i) = \varepsilon/N\}$ be the coordinates at the floor. Then there are numbers $\mu_1, \dots, \mu_N$ such that
--
--   $$x(i) = y(i)\, e^{\mu_i}\, C \quad\text{for all } i, \qquad C = \frac{1 - \frac{\varepsilon}{N}|S|}{\sum_{j \notin S} y(j)},$$
--
--   with $\mu_i \ge 0$ for all $i$ and $\mu_i = 0$ for $i \notin S$.
--
--   In words, the projection rescales $y$ by a common factor $C$ off the floor and lifts the remaining coordinates up to $\varepsilon/N$. This closed form is what the analysis of Algorithm 1 (Lemmas 1 and 2) uses to compare $h_{t+1}$ with $h_t$.
--
--   **Formalization Note** The positivity of $y$ is added (the paper writes $y \in \mathbb R^N_+$; the logarithm in the KL objective needs $y(i) > 0$). The complement of $S$ is nonempty because $\sum_i x(i) = 1 > \varepsilon$, so $C$ is a genuine quotient.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, p. 9, Proposition 1(b) (proof in Appendix A, pp. 25–26)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model

namespace CloudMWU.Bicriteria

open Finset

theorem proposition_1b (N : ℕ) (hN : 2 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (y : Fin N → ℝ) (hy : ∀ i, 0 < y i) (x : Fin N → ℝ) (hx : IsKLProj ε y x) :
    ∃ μ : Fin N → ℝ, (∀ i, 0 ≤ μ i) ∧
      (∀ i, x i ≠ ε / (N : ℝ) → μ i = 0) ∧
      ∀ i, x i = y i * Real.exp (μ i) *
        ((1 - ε / (N : ℝ) * ((univ.filter (fun j => x j = ε / (N : ℝ))).card : ℝ)) /
          ∑ j ∈ univ.filter (fun j => x j ≠ ε / (N : ℝ)), y j) := by sorry

end CloudMWU.Bicriteria
