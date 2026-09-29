-- Prove2me | Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite_univ
-- name    : Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/cc9d168b-c127-52ef-be35-a0a35290a058
-- title:
--   Finite algebra over a complete local ring splits into local factors
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is local and Noetherian and which is adically complete for its maximal ideal $\mathfrak{m}_{\mathcal{O}}$ (i.e. the completeness and separatedness conditions of `IsAdicComplete` hold for the $\mathfrak{m}_{\mathcal{O}}$-adic filtration), and let $A$ be a commutative $\mathcal{O}$-algebra that is finite as an $\mathcal{O}$-module. Then four assertions hold simultaneously. First, the maximal spectrum of $A$, the type `MaximalSpectrum A` of maximal ideals of $A$, is finite. Second, the ring homomorphism $A \to \prod_{I} A_{I}$ assembled from the localisation maps $A \to A_{I}$, the product being taken over all $I \in$ `MaximalSpectrum A` and $A_{I}$ denoting `Localization.AtPrime I.asIdeal`, is bijective, hence a ring isomorphism. Third, for each maximal ideal $I$ of $A$ the localisation $A_{I}$ is again finite as an $\mathcal{O}$-module. Fourth, for each maximal ideal $I$ of $A$ the local ring $A_{I}$ is adically complete for its own maximal ideal. No nonzeroness or connectedness hypothesis is imposed on $A$.
--
--   This is the structure theorem for module-finite algebras over a complete Noetherian local ring: such an algebra is semilocal and decomposes as the product of its localisations at its finitely many maximal ideals, each factor being module-finite and complete. It is what allows a localisation of a Hecke algebra at a maximal ideal to be treated as a direct factor, hence as a complete local $\mathcal{O}$-algebra finite over $\mathcal{O}$; within the development it feeds the construction of idempotents vanishing in a local quotient, via [`IsAdicComplete.exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient`](thm.html#IsAdicComplete.exists_isIdempotentElem_apply_eq_zero_isLocalRing_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite_univ.lean

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Noetherian.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite_univ
    {𝒪 : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type*) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal)) := by sorry
