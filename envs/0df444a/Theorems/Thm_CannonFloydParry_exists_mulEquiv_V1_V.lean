-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_V1_V
-- name    : CannonFloydParry.exists_mulEquiv_V1_V
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:29:08.84348+00:00
-- url     : https://prove2.me/theorems/90154f49-92df-4d95-9775-e74a7ac828f2
-- title:
--   p. 243 — $V_1 \cong V$, the symbols going to $A$, $B$, $C$, $\pi_0$
-- statement:
--   There is a group isomorphism $V_1 \cong V$ sending the formal symbols $A$, $B$, $C$, $\pi_0$ to the maps $A$, $B$, $C$, $\pi_0$ of the circle. Thus $V$ has the presentation of p. 242.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 243, after Lemma 6.1

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_mulEquiv_V1_V :
    ∃ e : V1 ≃* V, ∀ s, (e (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symV s := by
  sorry

end CannonFloydParry
