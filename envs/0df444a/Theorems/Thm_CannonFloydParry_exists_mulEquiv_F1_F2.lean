-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_F1_F2
-- name    : CannonFloydParry.exists_mulEquiv_F1_F2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:43:47.629254+00:00
-- url     : https://prove2.me/theorems/981b7e28-6101-4a12-bb3d-66d4403a3b99
-- title:
--   Theorem 3.1: $F_1 \cong F_2$ with $A \mapsto X_0$, $B \mapsto X_1$
-- statement:
--   There is a group isomorphism from $F_1 = \langle A, B : [AB^{-1}, A^{-1}BA],\ [AB^{-1},
--   A^{-2}BA^{2}]\rangle$ onto $F_2 = \langle X_0, X_1, \dots : X_k^{-1} X_n X_k = X_{n+1}\ (k<n)\rangle$
--   sending the formal symbol $A$ to $X_0$ and $B$ to $X_1$. The statement asserts the existence of
--   such an isomorphism; it does not name one, and it says nothing about uniqueness (which follows
--   from $A$, $B$ generating $F_1$).
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 225, Theorem 3.1

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Theorem 3.1: there is a group isomorphism `F₁ ≃ F₂` sending the formal symbol `A` to
`X₀` and `B` to `X₁`. -/
theorem exists_mulEquiv_F1_F2 :
    ∃ e : F1 ≃* F2, e (PresentedGroup.of FormalAB.A) = PresentedGroup.of 0 ∧
      e (PresentedGroup.of FormalAB.B) = PresentedGroup.of 1 := by
  sorry

end CannonFloydParry
