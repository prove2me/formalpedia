-- Prove2me | Theorems.Thm_CycBMWFree_Freeness_theorem_4_8
-- name    : CycBMWFree.Freeness.theorem_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:53.984204+00:00
-- url     : https://prove2.me/theorems/c2acb5ff-c183-4fa8-8e50-c992ec3bead2
-- title:
--   Theorem 4.8 (3), (4), (6), p. 35 — generic matrix decomposition
-- statement:
--   Over the generic field $F$, let $Γ_n$ be the multipartition shapes and let $T(n,λ)$ be the up–down tableaux of shape $λ$. For the generic parameters $P$, the cyclotomic BMW algebra has the split matrix decomposition
--   $$
--   W_{n,F,r}(P)\cong\prod_{λ\in Γ_n} M_{|T(n,λ)|}(F).
--   $$
--   This states split semisimplicity with simple blocks labeled by the source's shapes and sizes determined by its paths. **Formalization Note** It packages parts (3), (4), and (6) with the module dimensions stated on pp. 32 and 42. The direct-sum identification with $I_n\oplus H_n$, the branching-edge claim (5), and the tangle claims are outside this milestone.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, p. 35, Theorem 4.8 (3), (4), (6); pp. 32, 42, block dimensions

import Mathlib
import Definitions.Def_CycBMWFree_Freeness_Setting

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- The split matrix-block form of Theorem 4.8 (3), (4), (6), p. 35. -/
theorem theorem_4_8 (r : ℕ) (P : GroundParameters (GenericField r) r)
    (hP : IsGenericParameters P) (n : ℕ) :
    Nonempty (BMW P n ≃ₐ[GenericField r]
      ((la : Gamma r n) → Matrix (Fin (Nat.card (UpDown r n la.1)))
        (Fin (Nat.card (UpDown r n la.1))) (GenericField r))) := by sorry

end CycBMWFree.Freeness
