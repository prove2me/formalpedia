-- Prove2me | Theorems.Thm_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar
-- name    : DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/5e3702c7-0b12-58c7-951c-ca154f422a5c
-- title:
--   Dirichlet characters give finite-order Hecke characters of ℚ
-- statement:
--   Let $N$ be a natural number, nonzero, and let $\chi$ be a Dirichlet character modulo $N$ with values in $\mathbb{C}$. Associated with $\chi$ is the homomorphism [`DirichletCharacter.dirichletIdeleChar`](def/DirichletCharacter_DirichletIdeleChar.html#L125), namely the inverse of the composite of the unit homomorphism `unitResidue N` from the ideles $(\mathbb{A}_{\mathbb{Q}})^\times$ of $\mathbb{Q}$ — whose value at an idele $x$ is the element of $\mathbb{Z}/N\mathbb{Z}$ obtained from the family `unitResidues N x` of local residues through the inverse of the isomorphism `ZMod.equivPi` with the product of the $\mathbb{Z}/p^{k}\mathbb{Z}$ — with the unit-group homomorphism $(\mathbb{Z}/N\mathbb{Z})^\times \to \mathbb{C}^\times$ attached to $\chi$, so $x \mapsto \chi(\overline{u}_N(x))^{-1}$. The assertion is that this homomorphism $(\mathbb{A}_{\mathbb{Q}})^\times \to \mathbb{C}^\times$ satisfies the three conditions packaged in [`HeckeCharacter.IsFiniteOrderHeckeChar`](def/HeckeCharacter_FiniteOrder.html#L13) for the field $\mathbb{Q}$: it is an idele class character, that is, it takes the value $1$ on the image of every $u \in \mathbb{Q}^\times$ under the map of unit groups induced by $\mathbb{Q} \to \mathbb{A}_{\mathbb{Q}}$; it is continuous; and it is of finite order in the group of such homomorphisms.
--
--   This records that the idele class character attached to a Dirichlet character modulo $N$ is a Hecke character of $\mathbb{Q}$ of finite order, supplying in particular the continuity and finite-order clauses that the construction of the character itself does not address. It is used when nebentypus data for classical modular forms is transported to the adelic setting, for instance in the identification of the central character of an adelic lift of a form on $\Gamma_1(N)$ and in the finite-dimensionality of cuspidal constituents.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_DirichletCharacter_isFiniteOrderHeckeChar_dirichletIdeleChar.lean

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_DirichletCharacter_DirichletIdeleChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem DirichletCharacter.isFiniteOrderHeckeChar_dirichletIdeleChar {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) : HeckeCharacter.IsFiniteOrderHeckeChar ℚ χ.dirichletIdeleChar := by sorry
