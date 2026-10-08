-- Prove2me | Theorems.Thm_Disjunctive_SequentialConvex_constraint_boundary_condition_v2
-- name    : Disjunctive.SequentialConvex.constraint_boundary_condition_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T22:06:08.106498+00:00
-- url     : https://prove2.me/theorems/22a83a8f-29ac-45c0-ae70-68b5aa9ceb8c
-- title:
--   Theorem 3.3 — the constraint boundary condition
-- statement:
--   This is Theorem 3.3 of Balas's *Disjunctive Programming*: the exact condition under which one step of sequential convexification is valid.
--
--   Let $F_{j-1} \subseteq \mathbb{R}^n$, let $D_j := \bigvee_{i \in Q_j} (d_i x \ge d_{i0})$, i.e. $D_j = \bigcup_{i\in Q_j}\{x : d_i x \ge d_{i0}\}$, and let $\bar D_j := \{x : d_i x \le d_{i0},\ i \in Q_j\}$ be the system obtained by reversing every inequality of $D_j$ (the closure of the complement of $D_j$). Then
--   $$
--   \mathrm{conv}\big[(\mathrm{conv}\,F_{j-1}) \cap D_j\big] = \mathrm{conv}(F_{j-1} \cap D_j) \tag{3.5}
--   $$
--   holds if and only if the **constraint boundary condition** holds: for every $x \in F_{j-1} \cap \bar D_j$ and $y \in F_{j-1} \cap D_j$,
--   $$
--   [x, y] \cap \mathrm{bd}(\bar D_j) \subseteq \mathrm{conv}(F_{j-1} \cap D_j), \tag{3.6}
--   $$
--   where $\mathrm{bd}(\bar D_j)$ is the boundary of $\bar D_j$ relative to the affine space spanned by $\bar D_j$.
--
--   **Formalization Note.** The retired version defined $\bar D_j$ as the union $\bigcup_i \{d_i x \le d_{i0}\}$, whose boundary need not be where segments from outside $D_j$ enter $D_j$; with the terms $x \ge 0$, $x \ge 1$ in $\mathbb{R}$ and $F_{j-1} = \{-1, \tfrac12\}$, (3.6) held vacuously while (3.5) failed. The corrected definition `Dbarj` (module `Disjunctive_SequentialConvex_Basic_v2`) is the conjunction $\bigcap_i \{d_i x \le d_{i0}\}$ of the reversed inequalities, the convex set $C_j$ with $\mathbb{R}^n \setminus D_j = \{x : d_i x < d_{i0}\ \forall i\}$; the theorem is the reverse-convex result of Balas, Tama and Tind (1989) for $x \notin \operatorname{int} C_j$. The relative boundary is Mathlib's `intrinsicFrontier`; the book's "$\in$" in (3.6) is read as set inclusion. $F_{j-1}$ is an arbitrary set, as in the retired statement (the equivalence holds for every $F_{j-1}$).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, §3.2, p. 46, Theorem 3.3 (Balas, Tama, Tind 1989) — D̄_j read as the conjunction of the reversed inequalities

import Mathlib
import Definitions.Def_Disjunctive_SequentialConvex_Basic_v2

namespace Disjunctive.SequentialConvex

/-- Theorem 3.3 (Balas, *Disjunctive Programming*, Springer 2018, §3.2, p. 46; Balas, Tama and
Tind 1989): `F_{j-1}` and `D_j = ⋁_{i ∈ Q_j} (d_i x ≥ d_{i0})` satisfy the
sequential-convexifiability relation (3.5) `conv[(conv F_{j-1}) ∩ D_j] = conv(F_{j-1} ∩ D_j)` if
and only if they satisfy the constraint boundary condition (3.6): for every `x ∈ F_{j-1} ∩ D̄_j`
and `y ∈ F_{j-1} ∩ D_j`, every point where the segment `[x, y]` meets the boundary of `D̄_j`
(relative to the affine hull of `D̄_j`) lies in `conv(F_{j-1} ∩ D_j)`. Here
`D̄_j = {x : d_i x ≤ d_{i0}, i ∈ Q_j}` is the system with every inequality of `D_j` reversed.

Version 2: `D̄_j` is the conjunction of the reversed inequalities (`Dbarj` of
`Disjunctive_SequentialConvex_Basic_v2`), not their union; with the union, the terms `x ≥ 0`,
`x ≥ 1` in `ℝ` and `F = {-1, 1/2}` satisfied (3.6) vacuously while (3.5) failed. -/
theorem constraint_boundary_condition_v2 {n : ℕ} (Fjm1 : Set (Fin n → ℝ)) {Qj : Type*}
    [Fintype Qj] (d : Qj → Fin n → ℝ) (d0 : Qj → ℝ) :
    (convexHull ℝ (convexHull ℝ Fjm1 ∩ Dj d d0) = convexHull ℝ (Fjm1 ∩ Dj d d0)) ↔
      (∀ x ∈ Fjm1 ∩ Dbarj d d0, ∀ y ∈ Fjm1 ∩ Dj d d0,
        segment ℝ x y ∩ intrinsicFrontier ℝ (Dbarj d d0) ⊆ convexHull ℝ (Fjm1 ∩ Dj d d0)) := by sorry

end Disjunctive.SequentialConvex
