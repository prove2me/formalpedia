-- Prove2me | Theorems.Thm_CannonFloydParry_exists_toCircle_eq_of_mem_T_of_apply_zero
-- name    : CannonFloydParry.exists_toCircle_eq_of_mem_T_of_apply_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:45:29.432215+00:00
-- url     : https://prove2.me/theorems/8f315f7e-7398-423a-985f-484424f38c0f
-- title:
--   p. 235 — an element of $T$ fixing $[0]$ comes from $F$
-- statement:
--   If $f \in T$ fixes the point $[0]$ of the circle, then $f$ is induced by an element of $F$: there is $g \in F$ with $f[x] = [g(x)]$ for all $x \in [0,1)$.
--
--   **Formalization Note.** "Induced" is `toCircle g = f`. With the milestone before, this identifies $F$ with the stabilizer of $[0]$ in $T$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 235, proof of Lemma 5.2

import Mathlib
import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem exists_toCircle_eq_of_mem_T_of_apply_zero {f : Equiv.Perm UnitAddCircle} (hf : f ∈ T)
    (h0 : f 0 = 0) : ∃ g ∈ F, toCircle g = f := by
  sorry

end CannonFloydParry
