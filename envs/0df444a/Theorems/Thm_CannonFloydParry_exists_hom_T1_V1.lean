-- Prove2me | Theorems.Thm_CannonFloydParry_exists_hom_T1_V1
-- name    : CannonFloydParry.exists_hom_T1_V1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:23:42.523486+00:00
-- url     : https://prove2.me/theorems/536b5349-472d-452b-ab7f-22a2e4249c06
-- title:
--   $T_1$ maps to $V_1$, $A, B, C \mapsto A, B, C$
-- statement:
--   There is a group homomorphism $T_1 \to V_1$ sending the formal symbols $A$, $B$, $C$ of $T_1$ to those of $V_1$.
--
--   **Formalization Note.** $V_1$'s relators 1)–6) are $T_1$'s six relators rewritten. The source uses the map silently whenever it applies Lemmas 5.5, 5.6 or Theorem 5.7 inside $V_1$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 248, proof of Theorem 6.9

import Mathlib
import Definitions.Def_CannonFloydParry_T
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_hom_T1_V1 :
    ∃ φ : T1 →* V1, φ (PresentedGroup.of FormalABC.A) = PresentedGroup.of FormalV.A ∧
      φ (PresentedGroup.of FormalABC.B) = PresentedGroup.of FormalV.B ∧
      φ (PresentedGroup.of FormalABC.C) = PresentedGroup.of FormalV.C := by
  sorry

end CannonFloydParry
