-- Prove2me | Theorems.Thm_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits
-- name    : Deformation.ProartinianCat.isCorepresentable_of_preservesLimits
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/a60b7fd8-8cb2-55b3-a3a7-d22ac30e7159
-- title:
--   Limit-preserving functors on widehatC_𝒪 are corepresentable
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field is finite. Let [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44) be the category whose objects are types $R$ in the universe $u$ equipped with a commutative ring structure, a topology, an $\mathcal{O}$-algebra structure, and the property `IsLocalProartinianAlgebra 𝓞 R`, that is: $R$ is a topological ring, a local ring, pro-Artinian in the sense of the predicate [`IsProartinian`](def/Deformations_IsProartinian.html#L185), the structure map $\mathcal{O} \to R$ is a local homomorphism, and $R$ is a residue algebra over $\mathcal{O}$ ([`IsResidueAlgebra 𝓞 R`](def/Deformations_IsResidueAlgebra.html#L15)). Let $F$ be a functor from this category to $\mathbf{Type}\ u$ which preserves all small limits. The conclusion is that $F$ is corepresentable: there is an object $R$ of [`Deformation.ProartinianCat 𝓞`](def/Deformations_ProartinianCat.html#L44) together with a natural isomorphism between $F$ and the covariant hom-functor $\operatorname{Hom}(R, -)$ of the category. No hypothesis whatever is imposed on $F$ beyond preservation of limits; in particular $F$ is not assumed to arise from a deformation problem.
--
--   This is the general pro-representability criterion underlying the construction of universal deformation rings: over a base with finite residue field, corepresentability of a set-valued functor on the category of local pro-Artinian $\mathcal{O}$-algebras follows from preservation of small limits alone, the finiteness of the residue field entering through the finiteness of open quotients ([`IsProartinian.finite_quotient_of_isOpen`](thm.html#IsProartinian.finite_quotient_of_isOpen)). It is used to produce the universal object in [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData), so that any functor cut out by deformation conditions stable under small limits is automatically pro-representable.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_ProartinianCat_isCorepresentable_of_preservesLimits.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory IsLocalRing

universe u v

theorem Deformation.ProartinianCat.isCorepresentable_of_preservesLimits {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
  [Finite (IsLocalRing.ResidueField 𝓞)] (F : CategoryTheory.Functor (Deformation.ProartinianCat 𝓞) (Type u))
  [CategoryTheory.Limits.PreservesLimits F] : F.IsCorepresentable := by sorry
