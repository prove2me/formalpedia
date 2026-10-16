-- Prove2me | Theorems.Thm_CompetitiveChores_IndivisibleRounding_existence_competitive
-- name    : CompetitiveChores.IndivisibleRounding.existence_competitive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:58:13.201773+00:00
-- url     : https://prove2.me/theorems/3b656ec2-49a8-4b2f-a766-e1e90bd54fed
-- title:
--   §2.3, p. 14 — competitive allocations of chores exist; one maximizes Nash social welfare over Pareto optimal allocations
-- statement:
--   Existence of competitive allocations of chores.
--
--   Let $n\ge1$ agents divide $m\ge1$ chores, with values $v\in\mathbb R^{n\times m}_{<0}$ and budgets $b\in\mathbb R^n_{<0}$. Then there is a competitive allocation $z$ (Definition 3) which maximizes the Nash social welfare over all Pareto optimal allocations:
--
--   $$\prod_{i=1}^n |u_i(z'_i)|^{|b_i|}\ \le\ \prod_{i=1}^n |u_i(z_i)|^{|b_i|}\qquad\text{for every Pareto optimal } z'.$$
--
--   This is the first corollary of the geometric characterization of competitive allocations (Theorem 7, after Bogomolnaia, Moulin, Sandomirskiy and Yanovskaya, 2017): the competitive profiles are the critical points of the Nash social welfare on the strictly negative part of the Pareto frontier, and the maximum is such a point. In the proof of Theorem 34 the existence part is applied with budgets $b=-\beta$.
--
--   **Formalization Note** $n\ge1$ and $m\ge1$ are added: with $m=0$ no bundle can meet a strictly negative budget, and with $n=0$ and $m\ge1$ no feasible allocation exists. The page's justification ("the level curve first touches the Pareto frontier when we decrease $C$") is not formalized; only its conclusion is stated.
-- source:
--   Brânzei and Sandomirskiy, Algorithms for Competitive Division of Chores, arXiv:1907.01766v2, p. 14, §2.3, first paragraph

import Mathlib
import Definitions.Def_CompetitiveChores_IndivisibleRounding_Setting

namespace CompetitiveChores.IndivisibleRounding

/-- §2.3, p. 14: every chore division problem `(v, b)` with `v ∈ ℝ^{n×m}_{<0}` and `b ∈ ℝ^n_{<0}` has a
competitive allocation, and one of them maximizes the Nash social welfare `∏_i |u_i(z_i)|^{|b_i|}` over
all Pareto optimal allocations. -/
theorem existence_competitive {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (v : Fin n → Fin m → ℝ)
    (hv : ∀ i j, v i j < 0) (b : Fin n → ℝ) (hb : ∀ i, b i < 0) :
    ∃ z, CompetitiveChores.RichFamily.IsCompetitive v b z ∧
      ∀ z', CompetitiveChores.RichFamily.IsParetoOptimal v z' → nashWelfare v b z' ≤ nashWelfare v b z := by sorry

end CompetitiveChores.IndivisibleRounding
