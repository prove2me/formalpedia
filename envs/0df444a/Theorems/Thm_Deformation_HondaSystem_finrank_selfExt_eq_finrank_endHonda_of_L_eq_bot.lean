-- Prove2me | Theorems.Thm_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot
-- name    : Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/e3cf257e-783d-528e-bd4a-106acec544fd
-- title:
--   Self-extensions of an étale Honda system: dim Ext¹ = dim End
-- statement:
--   Let $k$ be a field and $D$ a finite-dimensional $k$-vector space, let $\ell \in k$ satisfy $\ell = 0$, and let $H$ be a Honda system with parameter $\ell$ on $D$, that is: $k$-linear endomorphisms $F, V$ of $D$ with $F \circ V = \ell \cdot \mathrm{id}$ and $V \circ F = \ell \cdot \mathrm{id}$, together with a subspace $L \subseteq D$ such that every $x \in L$ lying in the range of $F$ is of the form $\ell \cdot y$ with $y \in L$, every $y \in L$ has $\ell \cdot y$ in the range of $F$, the range of $F$ together with $L$ spans $D$, and $V$ is injective on $L$. Assume $L = 0$. Then the two $k$-dimensions agree: that of `H.selfExt`, the quotient of the space of pairs $(X,Y)$ of endomorphisms of $D$ satisfying $F \circ Y + X \circ V = 0$ and $V \circ X + Y \circ F = 0$ by the subspace of those pairs of the form $(F \circ a - a \circ F,\; V \circ a - a \circ V)$ with $a(L) \subseteq L$, and that of `H.endHonda`, the space of endomorphisms $a$ with $a(L) \subseteq L$ commuting with both $F$ and $V$.
--
--   This is the étale case of the dimension count for self-extensions of a finite Honda system over a field, in the explicit presentation of extensions by pairs of endomorphisms modulo inner derivations. It feeds into [`Deformation.HondaSystem.finrank_selfExt_le_finrank_endHonda_add_one`](thm.html#Deformation.HondaSystem.finrank_selfExt_le_finrank_endHonda_add_one), the linear-algebra form of the Fontaine–Laffaille bound for the dimension of the flat deformation space of a rank-two object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_HondaSelfExt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem Deformation.HondaSystem.finrank_selfExt_eq_finrank_endHonda_of_L_eq_bot
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [FiniteDimensional k D] {ℓ : k} (hℓ : ℓ = 0) (H : Deformation.HondaSystem ℓ D)
    (hL : H.L = ⊥) :
    Module.finrank k H.selfExt = Module.finrank k H.endHonda := by sorry
