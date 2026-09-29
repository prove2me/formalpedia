-- Prove2me | Theorems.Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite
-- name    : Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/48699e84-6451-5fb0-ba89-dc27897a3666
-- title:
--   Finite algebras over complete local rings split into local factors
-- statement:
--   Let $\mathcal{O}$ be a commutative ring which is local, noetherian, and adically complete with respect to its maximal ideal, and let $A$ be a commutative $\mathcal{O}$-algebra which is finite as an $\mathcal{O}$-module. The theorem asserts four statements simultaneously. First, the type `MaximalSpectrum A` of maximal ideals of $A$ is finite. Second, the ring homomorphism into the product over all $I \in \mathrm{MaximalSpectrum}\ A$ of the localisations $A_{I}$ at the maximal ideals, whose $I$-th component is the structure map $A \to A_{I}$, is bijective; that is, $A \to \prod_{I} A_{I}$ is a ring isomorphism. Third, for every maximal ideal $I$ of $A$, the localisation $A_{I}$ is again finite as an $\mathcal{O}$-module. Fourth, for every maximal ideal $I$ of $A$, the ring $A_{I}$ is adically complete with respect to its own maximal ideal (the maximal ideal of the local ring $A_I$). No separation or reducedness hypothesis on $A$ is imposed, and $A$ is not assumed local.
--
--   This is the standard structure theorem for module-finite algebras over a complete noetherian local ring: such an algebra is semilocal and decomposes as the finite product of its localisations at its maximal ideals, each factor being again module-finite and complete. In the formalisation it underlies the passage from a Hecke algebra to its local factor at a maximal ideal, and is cited in the construction of the localised Hecke algebras used in the Taylor–Wiles argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_finite_maximalSpectrum_and_bijective_localization_of_module_finite.lean

import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Noetherian.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Algebra.finite_maximalSpectrum_and_bijective_localization_of_module_finite
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (A : Type) [CommRing A] [Algebra 𝒪 A] [Module.Finite 𝒪 A] :
    Finite (MaximalSpectrum A) ∧
    Function.Bijective
      (RingHom.pi fun I : MaximalSpectrum A =>
        algebraMap A (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A, Module.Finite 𝒪 (Localization.AtPrime I.asIdeal)) ∧
    (∀ I : MaximalSpectrum A,
      IsAdicComplete (IsLocalRing.maximalIdeal (Localization.AtPrime I.asIdeal))
        (Localization.AtPrime I.asIdeal)) := by sorry
