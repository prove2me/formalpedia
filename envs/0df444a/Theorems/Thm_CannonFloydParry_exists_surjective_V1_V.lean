-- Prove2me | Theorems.Thm_CannonFloydParry_exists_surjective_V1_V
-- name    : CannonFloydParry.exists_surjective_V1_V
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:23:20.157918+00:00
-- url     : https://prove2.me/theorems/ef71973d-2fe0-40f8-92e9-13d765cd2b83
-- title:
--   p. 243 — a surjection $V_1 \to V$ sending the symbols to $A$, $B$, $C$, $\pi_0$
-- statement:
--   There is a surjective group homomorphism $V_1 \to V$ sending the formal symbols $A$, $B$, $C$, $\pi_0$ to the maps $A$, $B$, $C$, $\pi_0$ of the circle.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 243, after Lemma 6.1

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_surjective_V1_V :
    ∃ φ : V1 →* V, Function.Surjective φ ∧
      ∀ s, (φ (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symV s := by
  sorry

end CannonFloydParry
