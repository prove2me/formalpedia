-- Prove2me | Theorems.Thm_Disjunctive_IntroDuality_intersection_cut_v2
-- name    : Disjunctive.IntroDuality.intersection_cut_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:06.161355+00:00
-- url     : https://prove2.me/theorems/10482d1c-e26d-4cc6-9f07-884006d56688
-- title:
--   Theorem 1.1 — the intersection cut
-- statement:
--   This is Theorem 1.1 of Balas's *Disjunctive Programming*: the construction of an **intersection cut**, the origin of the subject.
--
--   Let $\iota$ index all (structural and surplus) variables of a linear program, and let $\bar x$ be a basic solution with basic index set $I$ and nonbasic index set $J$, where $I$ and $J$ partition $\iota$; thus $\bar x_j = 0$ for $j \in J$. Let $\bar a_{ij}$ be the simplex tableau's coefficients, so that the tableau reads $x_i = \bar x_i - \sum_{j \in J} \bar a_{ij} x_j$ ($i \in I$). The **LP cone** at $\bar x$ is
--   $$
--   C(J) := \Big\{x : x_i = \bar x_i - \sum_{j\in J} \bar a_{ij} x_j\ (i \in I),\ x_j \ge 0\ (j \in J)\Big\} = \bar x + \mathrm{cone}\{r^j : j \in J\},
--   $$
--   whose extreme-ray directions are $r^j$ with $r^j_j = 1$, $r^j_i = -\bar a_{ij}$ ($i \in I$) and $r^j_k = 0$ otherwise. The mixed-integer feasible set $P_I$ is contained in the LP relaxation, hence in $C(J)$.
--
--   Let $S$ be a convex set with $\bar x \in \operatorname{int} S$ and $\operatorname{int} S \cap P_I = \emptyset$, and for $j \in J$ let
--   $$
--   \lambda^*_j := \max\{\lambda_j : \bar x + \lambda_j r^j \in S\}.
--   $$
--   Then the **intersection cut**
--   $$
--   \sum_{j \in J} \frac{1}{\lambda^*_j}\, x_j \ \ge\ 1
--   $$
--   cuts off $\bar x$ (its left-hand side vanishes at $\bar x$) and is satisfied by every point of $P_I$.
--
--   **Formalization Note.** The retired version assumed only $x_j \ge 0$ ($j \in J$) on $P_I$ and did not require $I, J$ to partition the index set; with $J = \emptyset$ it then asserted $1 \le 0$ on any nonempty $P_I$ outside $\operatorname{int} S$. The new statement adds the book's setting explicitly: $I$ and $J$ are disjoint and cover $\iota$ (`hIJ`, `hcover`), and every point of $P_I$ lies in the LP cone $C(J)$ (`hPI_cone`: the tableau equations and nonnegativity of the nonbasic variables), which in the book follows from $P_I \subseteq P \subseteq C(J)$ (the tableau is an equivalent rewriting of the LP's equality system; $C(J)$ only drops the nonnegativity of the basic variables). As before, $\lambda^*_j$ is the maximum of $\{t : \bar x + t r^j \in S\}$ (`IsGreatest`), i.e. the theorem is stated for the case in which these maxima exist, as in the book's formula; $\lambda^*_j > 0$ follows from $\bar x \in \operatorname{int} S$. With $J = \emptyset$ the new hypotheses force $P_I \subseteq \{\bar x\} \subseteq \operatorname{int} S$, so $P_I = \emptyset$ and the statement holds.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §1.2, p. 4, Theorem 1.1 (Balas 1971, Oper. Res. 19)

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_IntersectionCut

namespace Disjunctive.IntroDuality

/-- Theorem 1.1 (Balas, *Disjunctive Programming*, Springer 2018, §1.2, p. 4; Balas 1971 [4]):
the intersection cut. Let `x̄` be a basic solution of the LP relaxation, with basic index set `I`
and nonbasic index set `J` partitioning the full index set `ι` of structural and surplus
variables, so that `x̄_j = 0` for `j ∈ J`, and let `ā` be the simplex tableau's coefficients.
Every point of `P_I` lies in the LP cone
`C(J) = {x : x_i = x̄_i - Σ_{j ∈ J} ā_{ij} x_j (i ∈ I), x_j ≥ 0 (j ∈ J)} = x̄ + cone{r^j : j ∈ J}`
(`P_I ⊆ P ⊆ C(J)`: the tableau rows are an equivalent rewriting of the LP's equations, and `C(J)`
drops only the nonnegativity of the basic variables). If `S` is a convex set with `x̄ ∈ int S`
and no point of `P_I` in `int S`, and `λ*_j = max {λ : x̄ + λ r^j ∈ S}` for `j ∈ J`, then the
cut `Σ_{j ∈ J} x_j / λ*_j ≥ 1` cuts off `x̄` and is satisfied by every point of `P_I`.

Version 2: the retired statement did not require `I, J` to partition `ι` nor `P_I ⊆ C(J)`
(only `x_j ≥ 0` on `J`), so with `J = ∅` it claimed `1 ≤ 0` on any nonempty `P_I`. -/
theorem intersection_cut_v2 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I J : Finset ι) (hIJ : Disjoint I J) (hcover : ∀ i : ι, i ∈ I ∨ i ∈ J)
    (abar : ι → ι → ℝ) (xbar : ι → ℝ) (PI S : Set (ι → ℝ))
    (hPIFree : PIFree S PI xbar)
    (hxbarJ : ∀ j ∈ J, xbar j = 0)
    (hPI_cone : ∀ x ∈ PI,
      (∀ i ∈ I, x i = xbar i - ∑ j ∈ J, abar i j * x j) ∧ ∀ j ∈ J, 0 ≤ x j)
    (lam : ι → ℝ)
    (hlam_max : ∀ j ∈ J, IsGreatest {t : ℝ | xbar + t • extremeRay I abar j ∈ S} (lam j)) :
    (∑ j ∈ J, (lam j)⁻¹ * xbar j) < 1 ∧ ∀ x ∈ PI, 1 ≤ ∑ j ∈ J, (lam j)⁻¹ * x j := by sorry

end Disjunctive.IntroDuality
