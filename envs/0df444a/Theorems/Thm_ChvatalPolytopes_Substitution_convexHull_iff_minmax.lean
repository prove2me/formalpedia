-- Prove2me | Theorems.Thm_ChvatalPolytopes_Substitution_convexHull_iff_minmax
-- name    : ChvatalPolytopes.Substitution.convexHull_iff_minmax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:57:44.312233+00:00
-- url     : https://prove2.me/theorems/632d1e97-e353-4957-9f09-236be41a864e
-- title:
--   Proposition 2.1 — convex hull via LP min–max for integer objectives
-- statement:
--   Let $V$ and $J$ be finite index sets, $a_{iu}$ and $b_i$ ($i\in J$, $u\in V$) real numbers, and consider the linear system
--   $$-x_u\le 0\quad(u\in V),\qquad \sum_{u\in V}a_{iu}x_u\le b_i\quad(i\in J).\tag{2.1}$$
--   Let $S$ be a finite nonempty set of solutions of (2.1). Then the set of all solutions of (2.1) is the convex hull of $S$ if and only if, for every integer-valued vector $c=(c_u:u\in V)$,
--   $$\max\{cx : x\in S\}=\min\Big\{\sum_{i\in J}\lambda_ib_i \;:\; \lambda_i\ge0 \text{ for all } i\in J,\ \sum_{i\in J}\lambda_ia_{iu}\ge c_u \text{ for all } u\in V\Big\}.$$
--
--   The proposition converts "(2.1) is a defining linear system of $\operatorname{conv}S$" into a family of min–max equalities, one for each integral objective. The proof of Theorem 5.1 applies it four times: once to each of $G_1$, $G_2$ to obtain dual multipliers, and once more to conclude that (5.1) defines $P(G)$.
--
--   **Formalization Note** "min = max" is stated as two clauses: every feasible $\lambda\ge0$ has $\sum_i\lambda_ib_i\ge\max_{x\in S}cx$, and some feasible $\lambda\ge0$ attains equality. The hypothesis that $S$ is nonempty is added (the paper's $\max\{cx:x\in S\}$ requires it). The nonnegativity rows $-x_u\le0$ are kept, as a separate conjunct $x\ge0$ of the solution set; without them the statement is false. $J$ is a finite type and $a,b$ are real; $c$ ranges over $\mathbb Z^V$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), pp. 139–140, Proposition 2.1

import Mathlib

namespace ChvatalPolytopes.Substitution

/-- **Proposition 2.1** (Chvátal 1975, pp. 139–140). Let `S` be a finite set of solutions
`x = (x_u : u ∈ V)` of the system (2.1)
`−x_u ≤ 0 (u ∈ V)`, `Σ (a_{iu} x_u : u ∈ V) ≤ b_i (i ∈ J)`.
Then the set of all solutions of (2.1) is the convex hull of `S` if and only if, for every
integer-valued vector `c = (c_u : u ∈ V)`,
`max {cx : x ∈ S} = min {Σ (λ_i b_i : i ∈ J) : λ_i ≥ 0 for all i ∈ J and
Σ (λ_i a_{iu} : i ∈ J) ≥ c_u for all u ∈ V}`.

"min = max" is stated as: (a) every feasible `λ` has objective `≥ max_{x ∈ S} cx`, and (b) some
feasible `λ` has objective equal to it. The hypothesis `S.Nonempty` is added (the paper's
`max {cx : x ∈ S}` requires it). The nonnegativity rows `−x_u ≤ 0` are kept as the conjunct
`∀ u, 0 ≤ x u`; `J` is a finite index type and the coefficients `a`, `b` are real. -/
theorem convexHull_iff_minmax {V : Type*} [Fintype V] {J : Type*} [Fintype J]
    (a : J → V → ℝ) (b : J → ℝ) (S : Finset (V → ℝ)) (hS : S.Nonempty)
    (hSsol : ∀ x ∈ S, (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a i u * x u ≤ b i} = convexHull ℝ (S : Set (V → ℝ)) ↔
      ∀ c : V → ℤ,
        (∀ lam : J → ℝ, (∀ i, 0 ≤ lam i) → (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) →
          S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u) ≤ ∑ i, lam i * b i) ∧
        (∃ lam : J → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ u, (c u : ℝ) ≤ ∑ i, lam i * a i u) ∧
          ∑ i, lam i * b i = S.sup' hS (fun x => ∑ u, (c u : ℝ) * x u)) := by sorry

end ChvatalPolytopes.Substitution
