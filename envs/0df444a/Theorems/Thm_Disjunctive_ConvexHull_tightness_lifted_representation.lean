-- Prove2me | Theorems.Thm_Disjunctive_ConvexHull_tightness_lifted_representation
-- name    : Disjunctive.ConvexHull.tightness_lifted_representation
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:11:45.361755+00:00
-- url     : https://prove2.me/theorems/9adb667b-cf3c-4d37-b801-9f15c4736ba5
-- title:
--   Theorem 2.3 — tightness of the lifted representation
-- statement:
--   This is Theorem 2.3 of Balas's *Disjunctive Programming*: a criterion for when the practical
--   inconvenience of Theorem 2.1's lifted representation — needing to know in advance which $P_h$
--   are nonempty, in order to index the lifting by $Q^*$ rather than all of $Q$ — can be avoided.
--
--   Let $P_Q$ denote the lifted polyhedron $(2.1)_Q$ obtained by indexing over all of $Q$ instead
--   of $Q^*$, and let $P$ denote the original lifted polyhedron $(2.1)$ indexed by $Q^*$. Then
--
--   $$
--   P_Q = P \iff C_k \subseteq \sum_{h \in Q^*} C_h \quad \text{for every } k \in Q \setminus Q^*,
--   $$
--
--   where $C_h$ is the recession cone of $P_h$. In words: the "safe" lifting over the full index
--   set $Q$ (which requires no advance knowledge of which disjuncts are feasible) coincides with
--   the lifting over only the feasible disjuncts exactly when every infeasible disjunct's
--   recession cone is already swallowed by the Minkowski sum of the feasible disjuncts' recession
--   cones — automatically true, in particular, whenever $F$ is a union of *polytopes* (bounded
--   polyhedra), since then every recession cone is $\{0\}$.
--
--   **Formalization Note.** `LiftedPolyhedron m A b Set.univ` is $(2.1)_Q$ (the same definition,
--   instantiated at $Q_{\mathrm{idx}} = Q$); `LiftedPolyhedron m A b (FeasibleIndices m A b)` is
--   $(2.1)$ itself.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 22, Theorem 2.3

import Mathlib
import Definitions.Def_Disjunctive_ConvexHull_Polyhedra
import Definitions.Def_Disjunctive_ConvexHull_LiftedPolyhedron

namespace Disjunctive.ConvexHull

/-- Theorem 2.3 (Balas §2.1, p. 22): `P_Q = P` if and only if every disjunct's recession cone
outside `Q*` is contained in the Minkowski sum of the recession cones inside `Q*`. `P` is the
`x`-set of Theorem 2.1, the projection of the lifted polyhedron over `Q*`, and `P_Q` the same
projection with `Q` substituted for `Q*`; the book's proof computes `P_Q = P + Σ_{k ∉ Q*} C_k`,
an identity in `x`-space. Equality of the *lifted* sets is a strictly stronger claim that holds
only when every dropped cone is `{0}`. -/
theorem tightness_lifted_representation {n : ℕ} {Q : Type*} [Fintype Q] (m : Q → ℕ)
    (A : (h : Q) → Matrix (Fin (m h)) (Fin n) ℝ) (b : (h : Q) → Fin (m h) → ℝ) :
    ProjX (LiftedPolyhedron m A b Set.univ) = ProjX (LiftedPolyhedron m A b (FeasibleIndices m A b)) ↔
      ∀ k, k ∉ FeasibleIndices m A b →
        RecessionCone (A k) ⊆ MinkowskiSumOver (FeasibleIndices m A b) (fun h => RecessionCone (A h)) := by sorry

end Disjunctive.ConvexHull
