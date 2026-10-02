-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexSets_discrete_separation_lconvex
-- name    : DiscreteConvex.LConvexSets.discrete_separation_lconvex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T22:36:58.126985+00:00
-- url     : https://prove2.me/theorems/8a59935a-ae2d-446b-ab5e-74aeafdc492d
-- title:
--   Theorem 5.9 -- discrete separation for L-convex sets
-- statement:
--   **Theorem 5.9** (p.126). Let $D_1, D_2 \subseteq \mathbb Z^V$ be L-convex sets. If they are disjoint, there exists $x^* \in \{-1,0,1\}^V$ such that
--
--   $$\inf\{\langle p, x^*\rangle : p \in D_1\} - \sup\{\langle p, x^*\rangle : p \in D_2\} \ge 1.$$
--
--   An ordinary separating hyperplane exists for any two disjoint convex sets; the content here is that the separator can always be forced into $\{-1,0,1\}^V$ — three values per coordinate — independent of how large or awkwardly shaped $D_1, D_2$ are. A formalization proving only the classical real-valued separation (any $x^* \in \mathbb R^V$) would state nothing specific to discrete convexity.
--
--   **Formalization Note.** The conclusion is stated as $\sup_{D_2}\langle p,x^*\rangle + 1 \le \inf_{D_1}\langle p,x^*\rangle$ (addition) rather than $\inf - \sup \ge 1$ (subtraction), an equivalent reformulation that avoids `EReal` subtraction's `⊤ - ⊤` ambiguity; the infimum and supremum are taken in `EReal` (a complete lattice) so that both are total even though $D_1, D_2$ may be unbounded (L-convex sets are always translation-invariant along the all-ones direction, hence typically infinite).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.126, Theorem 5.9.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.126, Theorem 5.9

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexSets_LConvexSet

namespace DiscreteConvex.LConvexSets

/-- Theorem 5.9 (discrete separation for L-convex sets; Murota, *Discrete Convex Analysis*,
SIAM 2003, p.126). Let `D1, D2 ⊆ Zⱽ` be L-convex sets. If they are disjoint, there exists
`x* ∈ {-1,0,1}ⱽ` such that `inf{⟨p,x*⟩ : p ∈ D1} - sup{⟨p,x*⟩ : p ∈ D2} ≥ 1`. -/
theorem discrete_separation_lconvex {V : Type*} [Fintype V] [DecidableEq V]
    (D1 D2 : Set (V → ℤ)) (hD1 : LConvexSet D1) (hD2 : LConvexSet D2)
    (hdisj : D1 ∩ D2 = ∅) :
    ∃ x : V → ℤ, (∀ v, x v = -1 ∨ x v = 0 ∨ x v = 1) ∧
      sSup ((fun p : V → ℤ => ((∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D2) + 1 ≤
        sInf ((fun p : V → ℤ => ((∑ v, (x v : ℝ) * (p v : ℝ) : ℝ) : EReal)) '' D1) := by sorry

end DiscreteConvex.LConvexSets
