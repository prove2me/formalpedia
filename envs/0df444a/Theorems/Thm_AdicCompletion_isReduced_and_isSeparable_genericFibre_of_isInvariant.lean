-- Prove2me | Theorems.Thm_AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant
-- name    : AdicCompletion.isReduced_and_isSeparable_genericFibre_of_isInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/7973b3da-c319-51bd-befe-022f72735d37
-- title:
--   Reducedness and separability of the completed generic fibre
-- statement:
--   Let $O$ be a Noetherian local commutative ring with maximal ideal $\mathfrak m_O$, and let $C$ be a commutative domain that is an $O$-algebra, module-finite over $O$, with $O \to C$ injective (faithful scalar multiplication). Let $G$ be a finite group acting on $C$ by ring automorphisms, the action commuting with that of $O$ and faithful, and suppose $O$ is the ring of $G$-invariants of $C$ in the sense of `Algebra.IsInvariant`. Let $\mathfrak n$ be a maximal ideal of $C$ lying over $\mathfrak m_O$. Write $\hat O$ for the $\mathfrak m_O$-adic completion of $O$ and $\hat C_{\mathfrak n}$ for the $\mathfrak n$-adic completion of $C$. Let $K_0$ be a field that is a fraction field of $\hat O$, and let $F$ be a commutative ring which is simultaneously an $\hat C_{\mathfrak n}$-algebra, an $\hat O$-algebra and a $K_0$-algebra, compatibly (both towers $\hat O \to \hat C_{\mathfrak n} \to F$ and $\hat O \to K_0 \to F$ commuting), and which is a localisation of $\hat C_{\mathfrak n}$ at the image of the non-zero-divisors of $\hat O$; that is, $F = \hat C_{\mathfrak n} \otimes_{\hat O} K_0$ realised as such a localisation. Then $F$ is reduced and $F$ is separable as a $K_0$-algebra.
--
--   This is the statement that the generic fibre of the completion of a module-finite Galois cover $C/O$ at a maximal ideal above $\mathfrak m_O$ is a finite separable algebra over the fraction field of $\hat O$, the invariant-theoretic input being that $\operatorname{Frac} C/\operatorname{Frac} O$ is Galois. It feeds the proof that such completed localisations are integrally closed domains in the tame case, used in the local study of the deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isReduced_and_isSeparable_genericFibre_of_isInvariant.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isReduced_and_isSeparable_genericFibre_of_isInvariant {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (K₀ : Type) [Field K₀] [Algebra (AdicCompletion (maximalIdeal O) O) K₀] [IsFractionRing (AdicCompletion (maximalIdeal O) O) K₀]
    (F : Type) [CommRing F] [Algebra (AdicCompletion 𝔫 C) F] [Algebra (AdicCompletion (maximalIdeal O) O) F] [Algebra K₀ F]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) F]
    [IsScalarTower (AdicCompletion (maximalIdeal O) O) K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C) (nonZeroDivisors (AdicCompletion (maximalIdeal O) O))) F] :
    IsReduced F ∧ Algebra.IsSeparable K₀ F := by sorry
