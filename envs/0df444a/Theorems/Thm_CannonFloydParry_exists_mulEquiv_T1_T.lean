-- Prove2me | Theorems.Thm_CannonFloydParry_exists_mulEquiv_T1_T
-- name    : CannonFloydParry.exists_mulEquiv_T1_T
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:49:20.223505+00:00
-- url     : https://prove2.me/theorems/b15ce2cd-2c80-481d-ac01-16840ce4913d
-- title:
--   Corollary 5.9 — $T_1 \cong T$, the symbols going to $A$, $B$, $C$
-- statement:
--   There is a group isomorphism $T_1 \cong T$ sending the formal symbols $A$, $B$, $C$ to the maps $A$, $B$, $C$ of the circle. Thus $T$ has the presentation of p. 236.
--
--   **Formalization Note.** The source states "$T_1$ is isomorphic to $T$" and says on p. 236 that the isomorphism is the surjection of Lemma 5.3; the statement names that map by its values on generators.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 240, Corollary 5.9

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem exists_mulEquiv_T1_T :
    ∃ e : T1 ≃* T, ∀ s, (e (PresentedGroup.of s) : Equiv.Perm UnitAddCircle) = symT s := by
  sorry

end CannonFloydParry
