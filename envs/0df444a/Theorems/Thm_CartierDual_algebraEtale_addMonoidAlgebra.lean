-- Prove2me | Theorems.Thm_CartierDual_algebraEtale_addMonoidAlgebra
-- name    : CartierDual.algebraEtale_addMonoidAlgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/656d1526-e840-5d8a-ae52-b639742d9578
-- title:
--   The Cartier dual of R[M] is étale for finite M
-- statement:
--   Let $R$ be a commutative ring and let $M$ be a finite additive abelian group. Form the additive monoid algebra $R[M]$ (`AddMonoidAlgebra R M`), a commutative $R$-algebra carrying its standard bialgebra structure, with comultiplication determined on the basis by $\Delta(\mathrm{single}\,x\,1) = \mathrm{single}\,x\,1 \otimes \mathrm{single}\,x\,1$. The project's [`CartierDual R A`](def/HopfAlgebra_CartierDual.html#L12), for a commutative bialgebra $A$ over $R$, is by definition the $R$-linear dual $\operatorname{Hom}_R(A, R)$, equipped with the convolution algebra structure transported from the dual: multiplication of functionals is induced by the comultiplication of $A$, the unit by the counit, and the structure map from $R$ by scaling the counit. The theorem asserts that the commutative $R$-algebra $\operatorname{CartierDual}_R(R[M]) = \operatorname{Hom}_R(R[M], R)$ with this convolution structure is étale over $R$, in Mathlib's sense of `Algebra.Etale`, namely formally étale and of finite presentation as an $R$-algebra.
--
--   Geometrically, $\operatorname{Spec} R[M]$ is the split finite group scheme of multiplicative type with character group $M$ (for $M = (\mathbb{Z}/m)^t$ it is $\mu_m^t$), and the assertion is that its Cartier dual, the constant group scheme attached to $M$, is étale; in this development the predicate `Algebra.Etale R (CartierDual R H)` is the working form of "$\operatorname{Spec} H$ is of multiplicative type". It is used to discharge that hypothesis for group algebras of finite abelian groups in the rigidity arguments for homomorphisms out of multiplicative-type groups, as in [`HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq`](thm.html#HopfAlgebra.bialgHom_addMonoidAlgebra_eq_of_mapAlgHom_residueField_comp_eq) and the results on the Néron model of the modular curve at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_algebraEtale_addMonoidAlgebra.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem CartierDual.algebraEtale_addMonoidAlgebra
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Finite M] :
    Algebra.Etale R (CartierDual R (AddMonoidAlgebra R M)) := by sorry
