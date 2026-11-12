-- Prove2me | Theorems.Thm_CayleyErdosGyarfas_feit_thompson
-- name    : CayleyErdosGyarfas.feit_thompson
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-11-12T02:10:08.439595+00:00
-- url     : https://prove2.me/theorems/b013ec11-2985-4700-85f4-b854b55db615
-- title:
--   Feit–Thompson theorem: every finite group of odd order is solvable
-- statement:
--   Let $G$ be a finite group of odd order. Then $G$ is solvable: its derived series $G = G^{(0)} \trianglerighteq G^{(1)} \trianglerighteq G^{(2)} \trianglerighteq \cdots$, defined by $G^{(i+1)} = [G^{(i)}, G^{(i)}]$, reaches the trivial subgroup after finitely many steps:
--
--   $$|G| \text{ odd} \;\Longrightarrow\; G^{(n)} = \{1\} \text{ for some } n \ge 0 .$$
--
--   This is the odd order theorem of Feit and Thompson (1963). The proof of Theorem 1.1 of the source paper (§2, p. 4) invokes it to conclude that a minimal counterexample to the claim made there (every Cayley graph of a noncyclic group of odd order contains a symmetric figure-eight) is solvable, so that its minimal normal subgroups are elementary abelian. It is a supporting statement of this mission, cited rather than proved by the paper, and Mathlib does not contain it.
--
--   **Formalization Note** Solvability is Mathlib's `Group.IsSolvable G`: some term `derivedSeries G n` of the derived series equals `⊥`. The type is that of `OddOrder.feitThompson` in Yawara Ishida's Lean 4 development (https://github.com/yawara/odd-order), a port of which is vendored and proved in Palomar entry PALOMAR-2026-11-04-000015.
-- source:
--   M. C. Burkhart, Odd-ordered Cayley graphs satisfy Erdős–Gyárfás, arXiv:2611.05060v1 (3 Nov 2026), https://arxiv.org/abs/2611.05060v1, §2, p. 4 (proof of Theorem 1.1: “By Feit–Thompson, G is solvable.”). The theorem itself is W. Feit and J. G. Thompson, Solvability of groups of odd order, Pacific J. Math. 13 (1963), 775–1029, https://doi.org/10.2140/pjm.1963.13.775. Lean type as `OddOrder.feitThompson` in https://github.com/yawara/odd-order (commit 7a412ea), vendored in Palomar entry PALOMAR-2026-11-04-000015 (https://palomar-registry.org/entry?id=PALOMAR-2026-11-04-000015).

import Mathlib.GroupTheory.Solvable
import Mathlib.SetTheory.Cardinal.Finite

namespace CayleyErdosGyarfas

/-- **Feit–Thompson theorem** (Feit–Thompson 1963): every finite group of odd order is
solvable. Supporting statement: the proof of Theorem 1.1 of arXiv:2611.05060v1 invokes it
(§2, p. 4). The type is that of `OddOrder.feitThompson` in Yawara Ishida's Lean 4
development. -/
theorem feit_thompson {G : Type*} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    Group.IsSolvable G := by sorry

end CayleyErdosGyarfas
