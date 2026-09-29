-- Prove2me | Theorems.Thm_CannonFloydParry_relsF1_lift_eq_one_F2
-- name    : CannonFloydParry.relsF1_lift_eq_one_F2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-17T20:40:16.206006+00:00
-- url     : https://prove2.me/theorems/90561662-4315-4606-8f33-3711e3dbe77f
-- title:
--   The relators of $F_1$ hold in $F_2$ under $A \mapsto X_0$, $B \mapsto X_1$
-- statement:
--   Under the assignment $A \mapsto X_0$, $B \mapsto X_1$ of formal symbols to elements of
--   $F_2$, extended to the free group on $\{A, B\}$, each of the two relators of $F_1$,
--   $$[AB^{-1}, A^{-1}BA] \quad\text{and}\quad [AB^{-1}, A^{-2}BA^{2}],$$
--   is sent to the identity of $F_2$. Equivalently, the assignment extends to a group homomorphism
--   $F_1 \to F_2$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 3, p. 225 (proof of Theorem 3.1, first paragraph)

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Definitions.Def_CannonFloydParry_Presentations
import Mathlib

namespace CannonFloydParry

/-- Theorem 3.1, first step: the defining relators of `F₁` hold in `F₂` under `A ↦ X₀`,
`B ↦ X₁`, so that assignment extends to a homomorphism `F₁ → F₂`. -/
theorem relsF1_lift_eq_one_F2 : ∀ r ∈ relsF1, FreeGroup.lift symF2 r = 1 := by
  sorry

end CannonFloydParry
