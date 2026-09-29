-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_F1_F
-- name    : CannonFloydParry.exists_mulEquiv_F1_F
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:47:11.768677+00:00
-- url     : https://prove2.me/theorems/5d71496c-dbce-474a-9bca-002b0c5e1ae8
-- title:
--   Theorem 3.4: $F_1 \cong F$ with $A \mapsto A$, $B \mapsto B$
-- statement:
--   There is a group isomorphism from $F_1 = \langle A, B : [AB^{-1}, A^{-1}BA],\ [AB^{-1},
--   A^{-2}BA^{2}]\rangle$ onto Thompson's group $F$ sending the formal symbol $A$ to the homeomorphism
--   $A$ and $B$ to $B$. This is the finite presentation of $F$. Existence of such an isomorphism is
--   asserted, nothing about uniqueness.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 226, Theorem 3.4 (the F₁ half)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Theorem 3.4 for `F₁`: there is a group isomorphism from
`F₁ = ⟨A, B : [AB⁻¹, A⁻¹BA], [AB⁻¹, A⁻²BA²]⟩` onto Thompson's group `F` sending the formal
symbols `A`, `B` to the functions `A`, `B`. -/
theorem exists_mulEquiv_F1_F :
    ∃ e : F1 ≃* F, ((e (PresentedGroup.of FormalAB.A) : F) : UI ≃o UI) = mapA ∧
      ((e (PresentedGroup.of FormalAB.B) : F) : UI ≃o UI) = mapB := by
  sorry

end CannonFloydParry
