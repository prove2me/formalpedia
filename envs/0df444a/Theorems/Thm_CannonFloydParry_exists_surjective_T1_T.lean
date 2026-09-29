-- Prove2me | Theorems.Thm_CannonFloydParry_exists_surjective_T1_T
-- name    : CannonFloydParry.exists_surjective_T1_T
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:46:35.731512+00:00
-- url     : https://prove2.me/theorems/d901ce61-4893-483d-860f-0d6421373432
-- title:
--   Lemma 5.3 — a surjection $T_1 \to T$ sending the symbols to $A$, $B$, $C$
-- statement:
--   There is a surjective group homomorphism $\varphi \colon T_1 \to T$ sending the formal symbols $A$, $B$, $C$ to the maps $A$, $B$, $C$ of the circle.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 236, Lemma 5.3

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem exists_surjective_T1_T :
    ∃ φ : T1 →* T, Function.Surjective φ ∧
      ∀ s, (φ (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symT s := by
  sorry

end CannonFloydParry
