-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_corner_polyhedron_vertex_cut_off_v2
-- name    : Disjunctive.GeneralDisjunctions.corner_polyhedron_vertex_cut_off_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:23.482631+00:00
-- url     : https://prove2.me/theorems/dae4deee-3f0b-451a-813b-e3fecbe04558
-- title:
--   Corollary 11.3 — every vertex of corner$(J)$ not a vertex of conv $P_I$ is cut off by a standard intersection cut
-- statement:
--   In the setting of Theorem 11.2 ($P=\{x: Ax=b,\ x\ge 0\}$ with rational data, $P_I=P\cap\{x_j\in\mathbb Z,\ j\in N'\}$), let $w$ be a vertex of $P$ with nonbasic set $J$ and tableau $\bar a$, and let $\operatorname{corner}(J)=\operatorname{conv}\big(C(J)\cap\{x_j\in\mathbb Z,\ j\in N'\}\big)$ be the corner polyhedron. Then every vertex $v$ of $\operatorname{corner}(J)$ that is not a vertex of $\operatorname{conv}P_I$ is cut off by some standard intersection cut: there exist a basic feasible solution $\bar x'$ of the LP (nonbasic set $J'$, tableau $\bar a'$) and a convex set $S$ that is $P_I$-free at $\bar x'$ such that the intersection cut $\sum_{j\in J'}x_j/\lambda^*_j\ge 1$ from $S$ and $C(J')$ is satisfied by every point of $P_I$ and violated by $v$.
--
--   **Formalization Note.** The retired version took $P_I$ to be an arbitrary set unrelated to the corner polyhedron (refuted by $P_I=(0,\infty)$, $v=0$) and derived the cut at $v$ itself from an arbitrary tableau; but $v$ (an integer point of $C(J)$ outside $P$) is not a basic solution of the LP, and an intersection cut is derived at a basic solution of the LP. Now $P_I$ is the mixed-integer set of $P$, the corner polyhedron is that of a vertex $w$ of $P$, and the cut comes from a basic feasible solution of the same LP. Validity of the cut for $P_I$ (Theorem 1.1) is stated so that a cut is actually named. The source states the corollary in one line ("It then follows"); the formal statement follows its wording ("not a vertex of conv $P_I$").
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §11.2, p. 152, Corollary 11.3 (= Balas–Kis 2016, remark after Theorem 13)

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Corner
import Definitions.Def_Disjunctive_GeneralDisjunctions_SIC

namespace Disjunctive.GeneralDisjunctions

/-- Corollary 11.3 (Balas, *Disjunctive Programming*, §11.2, p. 152; Balas–Kis 2016, after
Theorem 13: "every vertex of the corner polyhedron that is not a vertex of `conv P_I` is cut off
by some SIC"): let `w` be a vertex of `P` with cobasis `J` and tableau `ā`, and `v` a vertex of
the corner polyhedron `corner(J)` that is not a vertex of `conv P_I`. Then some standard
intersection cut cuts `v` off: there are a basic feasible solution `x̄'` of the LP (cobasis `J'`,
tableau `ā'`) and a convex set `S` that is `P_I`-free at `x̄'` such that the intersection cut from
`S` and `C(J')` is valid for `P_I` and violated by `v`.

Setting as in Theorem 11.2: `P = {x ∈ ℝ^ι : Ax = b, x ≥ 0}`, rational data,
`P_I = P ∩ {x_j ∈ ℤ, j ∈ N'}`, `corner(J) = conv(C(J) ∩ {x_j ∈ ℤ, j ∈ N'})`.

Corrected from the retired version, in which `P_I` was an arbitrary set unrelated to the corner
polyhedron (`P_I = (0, ∞)`, `v = 0` refuted it) and the cut was derived at `v` itself from an
arbitrary tableau rather than at a basic solution of the LP. -/
theorem corner_polyhedron_vertex_cut_off_v2 {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : IsRationalData A b) (Nprime : Finset ι)
    (I J : Finset ι) (abar : ι → ι → ℝ) (w : ι → ℝ)
    (hw : IsBasicFeasibleSolution A b I J abar w) (v : ι → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (cornerPolyhedron I J abar w Nprime))
    (hvPI : v ∉ Set.extremePoints ℝ (convexHull ℝ (MixedIntegerSet A b Nprime))) :
    ∃ (I' J' : Finset ι) (abar' : ι → ι → ℝ) (xbar' : ι → ℝ) (S : Set (ι → ℝ)),
      IsBasicFeasibleSolution A b I' J' abar' xbar' ∧
      PIFree S (MixedIntegerSet A b Nprime) xbar' ∧
      MixedIntegerSet A b Nprime ⊆ SICSet S I' J' abar' xbar' ∧
      v ∉ SICSet S I' J' abar' xbar' := by sorry

end Disjunctive.GeneralDisjunctions
