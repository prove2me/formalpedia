-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexSetsB_discrete_separation_mconvex
-- name    : DiscreteConvex.MConvexSetsB.discrete_separation_mconvex
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:31:22.102215+00:00
-- url     : https://prove2.me/theorems/b0e1201f-4e04-4b41-838a-32651c8c90aa
-- title:
--   Theorem 4.21 -- discrete_separation_mconvex
-- statement:
--   **Theorem 4.21** (Discrete separation for M-convex sets; p.114). GOAL. Let $B_1, B_2 \subseteq \mathbb Z^V$ be M-convex sets. If they are disjoint ($B_1 \cap B_2 = \emptyset$), there exists $p^* \in \{0,1\}^V \cup \{0,-1\}^V$ such that
--
--   $$\inf\{\langle p^*,x\rangle : x \in B_1\} - \sup\{\langle p^*,x\rangle : x \in B_2\} \ge 1.$$
--
--   The separating vector is not just any real vector but one whose entries are restricted to $\{0,1\}$ or, on the other branch, to $\{0,-1\}$: a strong combinatorial refinement of ordinary hyperplane separation, derived from Edmonds's intersection theorem (Theorem 4.18) via Frank's discrete separation theorem (Theorem 4.17).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.114, Theorem 4.21, Eq. (4.33).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.114, Theorem 4.21

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_ExchangeAxiomB

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.114, Theorem 4.21, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

/-- Theorem 4.21 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.114). See the item's
`natural_language_statement` for the full statement. -/
theorem discrete_separation_mconvex {V : Type*} [Fintype V] [DecidableEq V]
    (B1 B2 : Set (V → ℤ)) (hExc1 : ExchangeAxiomB B1) (hExc2 : ExchangeAxiomB B2)
    (hB1ne : B1.Nonempty) (hB2ne : B2.Nonempty) (hdisj : B1 ∩ B2 = ∅) :
    ∃ p : V → ℤ, ((∀ v, p v = 0 ∨ p v = 1) ∨ (∀ v, p v = 0 ∨ p v = -1)) ∧
      sInf ((fun x : V → ℤ => (∑ v, (p v : ℝ) * (x v : ℝ))) '' B1) -
        sSup ((fun x : V → ℤ => (∑ v, (p v : ℝ) * (x v : ℝ))) '' B2) ≥ 1 := by sorry

end DiscreteConvex.MConvexSetsB
