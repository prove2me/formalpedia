-- Prove2me | Theorems.Thm_Deformation_isLocalProartinianAlgebra_of_isAdicComplete
-- name    : Deformation.isLocalProartinianAlgebra_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/9a4caddb-0657-502c-939f-ce22b23704d3
-- title:
--   Complete Noetherian local 𝒪-algebras are pro-Artinian
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field is finite, and let $A$ be a commutative Noetherian local ring that is adically complete for its maximal ideal $\mathfrak{m}_A$ (Hausdorff and complete for the $\mathfrak{m}_A$-adic filtration), equipped with an $\mathcal{O}$-algebra structure whose structure map $\mathcal{O} \to A$ is a local homomorphism. Assume moreover that the composite of $\mathcal{O} \to A$ with the residue map $A \to A/\mathfrak{m}_A$ is surjective. Then, with $A$ carrying the $\mathfrak{m}_A$-adic topology, $A$ is a local pro-Artinian $\mathcal{O}$-algebra in the sense of the project's predicate [`Deformation.IsLocalProartinianAlgebra`](def/Deformations_ProartinianCat.html#L15), that is: $A$ is a topological ring and a local ring; the topology is linear over $A$ (it admits a basis of neighbourhoods of $0$ consisting of ideals), it is $T_0$, $A$ is complete for the associated uniformity, and for every open ideal $I$ of $A$ the quotient $A/I$ is an Artinian ring; the structure map $\mathcal{O} \to A$ is local; and the induced map $\mathcal{O} \to A/\mathfrak{m}_A$ on the residue field of $A$ is surjective.
--
--   This identifies the complete Noetherian local $\mathcal{O}$-algebras with residue field that of $\mathcal{O}$ — Mazur's category $\mathrm{CNL}_{\mathcal{O}}$ of coefficient rings — as objects of the category of local pro-Artinian $\mathcal{O}$-algebras in which deformation functors are represented. It is used in the Galois-representation deformation interface, by [`GaloisRep.exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy`](thm.html#GaloisRep.exists_algHom_baseChangeAlong_isEquiv_of_corepresentableBy) and [`GaloisRep.algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy`](thm.html#GaloisRep.algHom_unique_of_baseChangeAlong_isEquiv_of_corepresentableBy), to feed complete Noetherian local test objects into the representability machinery.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_isLocalProartinianAlgebra_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem Deformation.isLocalProartinianAlgebra_of_isAdicComplete
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [Algebra 𝒪 A] [IsLocalHom (algebraMap 𝒪 A)]
    (hres : Function.Surjective (IsLocalRing.residue A ∘ algebraMap 𝒪 A)) :
    @Deformation.IsLocalProartinianAlgebra 𝒪 _ A _ (maximalIdeal A).adicTopology _ := by sorry
