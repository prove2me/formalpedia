-- Prove2me | Theorems.Thm_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar
-- name    : DirichletCharacter.hasConductorExponentAt_localChar_dirichletIdeleChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/708fa969-2497-59c6-9d83-d7b2811c50a0
-- title:
--   Local conductor exponent of a primitive Dirichlet character's idele character
-- statement:
--   Let $N$ be a natural number with `NeZero N`, let $\chi :$ `DirichletCharacter ℂ N` be primitive (its conductor equals $N$), and let $v$ be a finite place of $\mathbb{Q}$, i.e. an element of the height one spectrum of the ring of integers $\mathcal{O}_{\mathbb{Q}}$. Let $\mu_\chi =$ `dirichletIdeleChar χ` be the character $(\mathbb{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$ given by the pointwise inverse of $x \mapsto \chi(\,$`unitResidue N`$\,x)$, where `unitResidue N` is the homomorphism from the ideles units to $\mathbb{Z}/N$ obtained from `unitResidues` through the Chinese-remainder identification `ZMod.equivPi`. Let `localChar` $\mu_\chi\, v$ be its local component at $v$: the character of $(\mathbb{Q}_v)^\times$ sending $t$ to the value of $\mu_\chi$ on the idele with component $t$ at $v$, $1$ at all other finite places and $1$ at the infinite place (via `localUnit` followed by `finIncl`). Put $c =$ `N.factorization (Ideal.absNorm v.asIdeal)`, the exponent of the residue characteristic of $v$ in $N$. The assertion is `HasConductorExponentAt ℚ v` for this local character with exponent $c$, that is: (i) the local character is trivial on `higherUnitsAt ℚ v c`, the set of units $u$ of $\mathbb{Q}_v$ with $|u| = 1$ and, unless $c = 0$, $|u - 1| \le \exp(-c)$; and (ii) for every $m < c$ there is $u \in$ `higherUnitsAt ℚ v m` on which it takes a value $\ne 1$.
--
--   This is the classical computation of the local conductor of the idele class character of $\mathbb{Q}$ attached to a primitive Dirichlet character: at each finite place the local conductor exponent is the exact power of the corresponding prime dividing the modulus. It is used in the converse-theorem part of the Langlands–Tunnell input, by [`LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le`](thm.html#LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le), to control the conductors of the twisting characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DirichletCharacter_hasConductorExponentAt_localChar_dirichletIdeleChar.lean

import Definitions.Def_DirichletCharacter_DirichletIdeleChar
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal

theorem DirichletCharacter.hasConductorExponentAt_localChar_dirichletIdeleChar
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (v : HeightOneSpectrum (RingOfIntegers ℚ)) :
    HasConductorExponentAt ℚ v (localChar (dirichletIdeleChar χ) v)
      (N.factorization (Ideal.absNorm v.asIdeal)) := by sorry
