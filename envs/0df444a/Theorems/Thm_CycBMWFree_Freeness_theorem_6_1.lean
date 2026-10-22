-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_theorem_6_1
-- name    : CycBMWFree.Freeness.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:59.313809+00:00
-- url     : https://prove2.me/theorems/22dc0367-5f46-400b-a9f1-3456ee67b193
-- title:
--   Theorem 6.1, p. 45 — free module of rank rⁿ(2n−1)!!
-- statement:
--   Let $S$ be an admissible integral ground ring with degree-$r$ parameters $P$. For every $n$, the cyclotomic Birman–Wenzl–Murakami algebra is free over $S$ of the stated rank:
--   $$
--   W_{n,S,r}(P)\cong_S S^{\,r^n(2n-1)!!}.
--   $$
--   The result gives the exact rank of the algebra over every admissible integral domain, not only over the generic field. **Formalization Note** The statement asserts a basis indexed by $\operatorname{Fin}(r^n(2n-1)!!)$; $r>0$ is part of the ground-parameter structure. The Kauffman-tangle isomorphism in the other half of the printed Theorem 6.1 is outside this mission.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, p. 45, Theorem 6.1

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- The freeness and rank assertion of Theorem 6.1, p. 45. -/
theorem theorem_6_1 {S : Type*} [CommRing S] [IsDomain S] {r : ℕ}
    (P : GroundParameters S r) (hP : BMWAdmissible P) (n : ℕ) :
    Nonempty (Module.Basis (Fin (rankN r n)) S (BMW P n)) := by sorry

end CycBMWFree.Freeness
