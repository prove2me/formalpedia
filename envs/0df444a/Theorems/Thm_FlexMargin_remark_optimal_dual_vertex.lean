-- Prove2me | Theorems.Thm_FlexMargin_remark_optimal_dual_vertex
-- name    : FlexMargin.remark_optimal_dual_vertex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:42:37.191397+00:00
-- url     : https://prove2.me/theorems/5ef01a0f-92ff-4a51-99a1-0f6d4fd3cae4
-- title:
--   Remark after Lemma 1: an optimal dual solution with prices in the margin-difference set
-- statement:
--   Let $C\ge0$, $d\in\mathbb R^n_+$, margins $p$ and a design $\mathcal A$ be given. Then the dual problem (3) has an optimal solution $(y^*,z^*)$ in which every product price lies in
--
--   $$
--   y^*_i\in\{p_i\}\cup\{0\}\cup\{p_i-p_{i'}: 1\le i'\le n,\ p_{i'}<p_i\}.
--   $$
--
--   This is what allows the DMGI (4) to restrict the prices to the values $\beta_{tr}$.
--
--   Differences from the source:
--   - encoding: capacities C_j (sign not stated) → hypothesis 0 ≤ C j; reason: with a negative capacity the LP (1) is infeasible and g is undefined; only excludes undefined cases
--   - encoding: margins p_i ∈ {P_1, …, P_T} → an arbitrary margin vector p : Fin n → ℝ; reason: every vector is P∘cat for the system whose margins are its distinct values; same instances
--   - encoding: an optimal solution to (3) → feasible and with objective at most that of every feasible pair; reason: definition of optimality spelled out
-- source:
--   Wang, Wang and Zhang, Robust Optimization Approach to Process Flexibility Designs with Contribution Margin Differentials, SSRN 3233721 (version of 2020-05-22), §3.1, remark after Lemma 1 (unnumbered), p. 16

import Mathlib
import Definitions.Def_FlexMargin_IsDualFeasible

namespace FlexMargin

/-- **Remark after Lemma 1: an optimal dual solution with prices in the margin-difference set.**
Wang, Wang and Zhang, *Robust Optimization Approach to Process Flexibility Designs with
Contribution Margin Differentials*, SSRN 3233721 (version of 2020-05-22), §3.1, remark after Lemma 1 (unnumbered), p. 16: "In view of Lemma 1, there must exist an
optimal solution (y∗,z∗) to the dual problem (3) where y∗i can only take one of the values from the
set {pi} ∪ {0} ∪ {pi − pi′ | 1 ≤ i′ ≤ n such that pi′ < pi} for each product i."

For capacities `C ≥ 0`, any margins `p`, design `A` and demand `d ≥ 0`, there is a feasible `(y, z)` for
(3) whose objective `Σ_i d_i y_i + Σ_j C_j z_j` is at most that of every feasible `(y', z')`, and with
`y_i ∈ {p_i} ∪ {0} ∪ {p_i − p_{i'} | p_{i'} < p_i}` for every product `i`.

**Formalization Note.** "Optimal" is stated directly: feasible and minimal among feasible points.
`d ≥ 0` is the paper's `d ∈ ℝ^n_+` (p. 16) and `C ≥ 0` the capacities' sign. -/
theorem remark_optimal_dual_vertex {m n : ℕ} (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (p : Fin n → ℝ) (A : Finset (Fin m × Fin n)) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    ∃ (y : Fin n → ℝ) (z : Fin m → ℝ), IsDualFeasible p A y z ∧
      (∀ (y' : Fin n → ℝ) (z' : Fin m → ℝ), IsDualFeasible p A y' z' →
        ∑ i, d i * y i + ∑ j, C j * z j ≤ ∑ i, d i * y' i + ∑ j, C j * z' j) ∧
      ∀ i, y i = p i ∨ y i = 0 ∨ ∃ i' : Fin n, p i' < p i ∧ y i = p i - p i' := by sorry

end FlexMargin
