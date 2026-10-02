-- Prove2me | Theorems.Thm_Disjunctive_IntroDuality_disjunctive_duality
-- name    : Disjunctive.IntroDuality.disjunctive_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:05:52.546974+00:00
-- url     : https://prove2.me/theorems/824b0aa1-3fce-429e-8193-9c9ce61f061d
-- title:
--   Theorem 1.5 — duality for disjunctive programs
-- statement:
--   This is Theorem 1.5 of Balas's *Disjunctive Programming*, generalizing the strong duality
--   theorem of linear programming to disjunctive programs — programs whose feasible region is a
--   union of finitely many polyhedra rather than a single one.
--
--   Let $Q$ be a finite index set and, for $h \in Q$, let $A_h$ be an $m_h \times n$ matrix and
--   $b_h \in \mathbb{R}^{m_h}$. The **disjunctive program**
--
--   $$
--   (DP)\qquad z_0 = \min\Big\{ c x \;:\; x \in \textstyle\bigcup_{h \in Q} X_h \Big\}, \qquad
--   X_h := \{x : A_h x \ge b_h,\ x \ge 0\},
--   $$
--
--   has as its **dual**
--
--   $$
--   (DD)\qquad w_0 = \max\Big\{ w \;:\; \forall h \in Q,\ \exists\, u_h \in U_h \text{ with } w \le
--   u_h b_h \Big\}, \qquad U_h := \{u_h \ge 0 : u_h A_h \le c\}.
--   $$
--
--   Let $Q^* := \{h : X_h \ne \emptyset\}$ and $Q^{**} := \{h : U_h \ne \emptyset\}$. Assume the
--   **Regularity Condition**: if $Q^* \ne \emptyset$ and $Q \setminus Q^{**} \ne \emptyset$, then
--   $Q^* \setminus Q^{**} \ne \emptyset$. Then **exactly one** of the following holds:
--
--   1. Both $(DP)$ and $(DD)$ are feasible, each attains an optimal value, and $z_0 = w_0$; or
--   2. one of the two problems is infeasible, and the other is either infeasible or has no finite
--      optimum (its objective is unbounded on its feasible region).
--
--   This is the disjunctive-programming analogue of the strong duality theorem of linear
--   programming, to which it reduces when $|Q| = 1$ (the Regularity Condition holding vacuously in
--   that case, since ordinary LP duality never fails except through infeasibility of both sides —
--   the classical case Corollary 1.6 pins down as the boundary of validity).
--
--   **Formalization Note.** The disjunction "exactly one of (1), (2)" is formalized as a logical
--   `Xor` of the two situations. Case (1) is stated as the existence of a single value $v$ that is
--   simultaneously the least value of $cx$ over the primal-feasible union and the greatest value
--   of $w$ over the dual-feasible pairs $(w, u)$ — which already forces both problems to attain an
--   optimum. Case (2) spells out, symmetrically in the primal and dual directions, "one is
--   infeasible, and the other is infeasible or unbounded", using the `UnboundedBelowOn` /
--   `UnboundedAboveOn` definitions for "has no finite optimum".
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 13-14, Theorem 1.5

import Mathlib
import Definitions.Def_Disjunctive_IntroDuality_PolyhedralSystems
import Definitions.Def_Disjunctive_IntroDuality_RegularityCondition
import Definitions.Def_Disjunctive_IntroDuality_OptimalValue

namespace Disjunctive.IntroDuality

/-- Theorem 1.5 (Balas §1.5, p. 13, [9, 10]): duality for disjunctive programs. `(DP)` is
`min {c x : x ∈ ⋃_{h ∈ Q} X_h}` and `(DD)` is `max {w : ∀ h, ∃ u_h ∈ U_h, w ≤ u_h b_h}`. Under
the Regularity Condition, exactly one of: (1) both are feasible, each attains an optimum, and
the optimal values agree; or (2) one is infeasible and the other is infeasible or unbounded. -/
theorem disjunctive_duality {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) (c : Fin n → ℝ)
    (hReg : RegularityCondition
              (FeasibleIndices (fun h => PolyNonneg (A h) (b h)))
              (FeasibleIndices (fun h => DualPoly (A h) c))) :
    Xor
      (∃ v : ℝ,
        IsLeast ((fun x => dotProduct c x) '' (⋃ h : Q, PolyNonneg (A h) (b h))) v ∧
        IsGreatest {w : ℝ | ∃ u : (h : Q) → Fin (m h) → ℝ,
                              ∀ h, u h ∈ DualPoly (A h) c ∧
                                w ≤ dotProduct (u h) (b h)} v)
      (((¬ (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty) ∧
          ((¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
                ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)) ∨
           UnboundedAboveOn {w : ℝ | ∃ u : (h : Q) → Fin (m h) → ℝ,
                                       ∀ h, u h ∈ DualPoly (A h) c ∧
                                         w ≤ dotProduct (u h) (b h)} id))
       ∨
       ((¬ ∃ w : ℝ, ∃ u : (h : Q) → Fin (m h) → ℝ,
              ∀ h, u h ∈ DualPoly (A h) c ∧ w ≤ dotProduct (u h) (b h)) ∧
          ((¬ (⋃ h : Q, PolyNonneg (A h) (b h)).Nonempty) ∨
           UnboundedBelowOn (⋃ h : Q, PolyNonneg (A h) (b h)) (fun x => dotProduct c x)))) := by sorry

end Disjunctive.IntroDuality
