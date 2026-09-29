-- Prove2me | Theorems.Thm_CannonFloydParry_toCircle_mem_T_and_mapC_mem_T
-- name    : CannonFloydParry.toCircle_mem_T_and_mapC_mem_T
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:44:44.529984+00:00
-- url     : https://prove2.me/theorems/bc64a5e4-9d68-44d1-9a4b-3fb2444ae0c1
-- title:
--   Example 5.1 — elements of $F$ induce elements of $T$, and $C \in T$
-- statement:
--   Every element $g$ of Thompson's group $F$ induces an element of $T$: the permutation $[x] \mapsto [g(x)]$ of the circle lies in $T$. In particular so do $A$ and $B$. The map $C$ of Example 5.1, $[x] \mapsto [x/2 + 3/4]$, $[2x - 1]$, $[x - 1/4]$ on $[0,\tfrac12)$, $[\tfrac12,\tfrac34)$, $[\tfrac34,1)$, lies in $T$.
--
--   **Formalization Note.** The source says this of $A$ and $B$; the statement is made for every $g \in F$, which is what the proof of Lemma 5.2 uses ("$F \subset H$").
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 234, Example 5.1

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem toCircle_mem_T_and_mapC_mem_T :
    (∀ f ∈ F, toCircle f ∈ T) ∧ mapC ∈ T := by
  sorry

end CannonFloydParry
