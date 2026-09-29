-- Prove2me | Theorems.Thm_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
-- name    : Algebra.isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/265be37d-88fb-5399-813c-1a40189dfb32
-- title:
--   Unramifiedness off the closed point passes to completions
-- statement:
--   Let $O$ be a commutative Noetherian local ring with maximal ideal $\mathfrak m$, let $C$ be a commutative ring that is an $O$-algebra and finite as an $O$-module, and let $\mathfrak n$ be a maximal ideal of $C$ lying over $\mathfrak m$. Let $S$ be a commutative local ring which is a $C$-algebra realising the localisation of $C$ at the prime $\mathfrak n$, equipped with an $O$-algebra structure compatible with $O \to C \to S$. Assume that for every prime ideal $\mathfrak q$ of $S$ which is not maximal, $S$ is unramified over $O$ at $\mathfrak q$, in the sense of `Algebra.IsUnramifiedAt`, i.e. the localisation of $S$ at $\mathfrak q$ is formally unramified over $O$. Then for every prime ideal $\mathfrak p$ of the $\mathfrak n$-adic completion $\widehat{C}$ of $C$ which is not maximal, $\widehat{C}$ is unramified at $\mathfrak p$ over the $\mathfrak m$-adic completion $\widehat{O}$ of $O$, the $\widehat{O}$-algebra structure on $\widehat{C}$ being the one furnished by the project's scoped instances for adic completions.
--
--   This is the statement that the property "unramified away from the closed point" is inherited by the $\mathfrak n$-adic completion of a module-finite algebra over a Noetherian local ring, via the identification of $\widehat{O}\otimes_O C$ with the product of the completions at the maximal ideals above $\mathfrak m$. It is used in the analysis of completed local models of modular curves, in the construction of the crossing model at a supersingular point and in the chart package for $X_1(N)/\Gamma_0(p)$-type integral models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_isUnramifiedAt_adicCompletion_of_forall_not_isMaximal.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem Algebra.isUnramifiedAt_adicCompletion_of_forall_not_isMaximal
    {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    [Algebra O S] [IsScalarTower O C S]
    (hunr : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt O 𝔮)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal) :
    Algebra.IsUnramifiedAt (AdicCompletion (maximalIdeal O) O) 𝔭 := by sorry
