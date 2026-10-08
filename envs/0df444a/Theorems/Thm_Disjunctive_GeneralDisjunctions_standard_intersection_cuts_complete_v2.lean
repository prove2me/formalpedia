-- Prove2me | Theorems.Thm_Disjunctive_GeneralDisjunctions_standard_intersection_cuts_complete_v2
-- name    : Disjunctive.GeneralDisjunctions.standard_intersection_cuts_complete_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:35.136478+00:00
-- url     : https://prove2.me/theorems/3a9e1c4c-4d24-421b-a470-71adefc6fe95
-- title:
--   Theorem 11.2 — every facet of conv $P_I$ cutting off a vertex of $P$ is a standard intersection cut
-- statement:
--   Let $P=\{x\in\mathbb R^\iota: Ax=b,\ x\ge 0\}$ be the LP relaxation, written in the space of structural and surplus variables, with rational data, and let $P_I=P\cap\{x: x_j\in\mathbb Z,\ j\in N'\}$. Let $F$ be a facet of $\operatorname{conv}P_I$ defined by the inequality $\varphi x\ge\varphi_0$ (valid for $P_I$), and suppose $F$ cuts off some vertex of $P$. Then $F$ is defined by a standard intersection cut: there is a vertex $v$ of $P$ with $\varphi v<\varphi_0$, with nonbasic set $J$ and simplex tableau $x_i=v_i-\sum_{j\in J}\bar a_{ij}x_j$ ($i\in I$), such that the halfspace $T=\{x:\varphi x\le\varphi_0\}$ is $P_I$-free at $v$ ($v\in\operatorname{int}T$, $\operatorname{int}T\cap P_I=\emptyset$) and the intersection cut
--   $$\sum_{j\in J}\frac{1}{\lambda^*_j}\,x_j\ \ge\ 1,\qquad \lambda^*_j=\sup\{t\ge 0: v+tr^j\in T\}\ \ (1/\infty:=0),$$
--   derived from $T$ and the LP cone $C(J)$ coincides with $\varphi x\ge\varphi_0$ on $\{x: Ax=b\}$, i.e. after the basic variables are expressed through the nonbasic ones.
--
--   **Formalization Note.** The retired version compared the intersection cut, an inequality in the nonbasic variables $x_J$ only, with $\varphi x\ge\varphi_0$ literally on all of $\mathbb R^\iota$, which is false whenever $\varphi$ has basic components (Balas compares them after substituting the tableau); it also had no link between the tableau and $P$, took $P_I$ to be an arbitrary subset of $P$ (then the theorem is false: $P=\mathbb R^2_+$, $P_I=\{1\}\times[0,1]$, facet at $(1,1)$ has a negative coefficient on a nonbasic variable), and assumed every extreme ray exits $T$. Now: the comparison is on the affine hull $\{Ax=b\}$ of the tableau; $P$, $P_I$, the vertex and its tableau are the book's objects (rational data, as assumed by Balas–Kis); a ray that never leaves $T$ gets coefficient $0$; and, as in the book's statement ("is defined by a standard intersection cut"), the vertex $v$ is existentially quantified — the proof takes a vertex minimizing $\varphi$ over $P$, at which every $\varphi r^j\ge 0$.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §11.2, p. 152, Theorem 11.2 (= Balas–Kis 2016, Theorem 13)

import Mathlib
import Definitions.Def_Disjunctive_GeneralDisjunctions_Basic
import Definitions.Def_Disjunctive_GeneralDisjunctions_Corner
import Definitions.Def_Disjunctive_GeneralDisjunctions_SIC

namespace Disjunctive.GeneralDisjunctions

/-- Theorem 11.2 (Balas, *Disjunctive Programming*, §11.2, p. 152, [25]; Balas–Kis 2016,
Theorem 13), the goal theorem of this mission: every facet of `conv P_I`, defined by
`φx ≥ φ0`, that cuts off some vertex of `P` is defined by a standard intersection cut. Precisely:
there is a vertex `v` of `P` cut off by the facet, with cobasis `J` and simplex tableau `ā`, such
that the halfspace `T := {x : φx ≤ φ0}` is `P_I`-free at `v` and the standard intersection cut
`∑_{j∈J} x_j/λ*_j ≥ 1` derived from `T` and the LP cone `C(J)` coincides with `φx ≥ φ0` on the
solution set of `Ax = b` (i.e. after substituting the tableau for the basic variables).

Setting (Balas Ch. 1/11): `P = {x ∈ ℝ^ι : Ax = b, x ≥ 0}` in the space of structural and
surplus variables, rational data, `P_I = P ∩ {x_j ∈ ℤ, j ∈ N'}`.

Corrected from the retired version, which compared the intersection cut (a constraint on the
nonbasic coordinates only) with `φx ≥ φ0` literally on all of `ℝ^ι`, had no link between the
tableau `ā` and `P`, took `P_I` to be an arbitrary subset of `P` (for which the theorem is
false), and assumed that every extreme ray exits `T` at a finite parameter (`λ*_j = ∞`, i.e.
coefficient `0`, is now allowed via `sicCoef`). -/
theorem standard_intersection_cuts_complete_v2 {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix (Fin m) ι ℝ) (b : Fin m → ℝ) (hrat : IsRationalData A b) (Nprime : Finset ι)
    (phi : ι → ℝ) (phi0 : ℝ)
    (hvalid : ∀ x ∈ MixedIntegerSet A b Nprime, phi0 ≤ dotProduct phi x)
    (hfacet : IsFacet (convexHull ℝ (MixedIntegerSet A b Nprime))
      {x ∈ convexHull ℝ (MixedIntegerSet A b Nprime) | dotProduct phi x = phi0})
    (hcutoff : ∃ v ∈ Set.extremePoints ℝ (LPFeasible A b), dotProduct phi v < phi0) :
    ∃ (I J : Finset ι) (abar : ι → ι → ℝ) (v : ι → ℝ),
      IsBasicFeasibleSolution A b I J abar v ∧ dotProduct phi v < phi0 ∧
      PIFree {x | dotProduct phi x ≤ phi0} (MixedIntegerSet A b Nprime) v ∧
      SICSet {x | dotProduct phi x ≤ phi0} I J abar v ∩ {x | A.mulVec x = b} =
        {x | phi0 ≤ dotProduct phi x} ∩ {x | A.mulVec x = b} := by sorry

end Disjunctive.GeneralDisjunctions
