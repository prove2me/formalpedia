-- Prove2me | Theorems.Thm_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable
-- name    : AdicCompletion.isField_localization_atPrime_of_not_isMaximal_of_isSeparable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/1a8e22b6-281d-53f8-98e5-c90bb7a273b1
-- title:
--   Analytic unramifiedness: widehatC_P is a field at non-maximal primes
-- statement:
--   Let $O$ be a discrete valuation ring which is a domain, and let $C$ be a domain which is an $O$-algebra, module-finite over $O$, with the $O$-action on $C$ faithful (so $O \to C$ is injective). Let $K$ and $L$ be fields which are fraction fields of $O$ and of $C$ respectively, equipped with compatible algebra structures making $O \to K \to L$ and $O \to C \to L$ scalar towers, and assume the extension $L/K$ is separable. Let $\mathfrak n$ be a maximal ideal of $C$ lying over the maximal ideal of the local ring $O$, and let $\widehat{C} = \operatorname{AdicCompletion} \mathfrak n\, C$ denote the $\mathfrak n$-adic completion of $C$. Then for every prime ideal $\mathfrak P$ of $\widehat{C}$ which is not maximal, the localisation of $\widehat{C}$ at $\mathfrak P$ is a field.
--
--   This is the analytic unramifiedness of a module-finite extension of a discrete valuation ring with separable generic fibre, in the form: the completion $\widehat{C}$ has field stalks at all non-maximal (in particular all minimal) primes, i.e. it is generically reduced. It feeds the verification that such localisations are regular local rings, used in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isField_localization_atPrime_of_not_isMaximal_of_isSeparable
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (K L : Type) [Field K] [Field L] [Algebra O K] [IsFractionRing O K] [Algebra C L] [IsFractionRing C L]
    [Algebra K L] [Algebra O L] [IsScalarTower O K L] [IsScalarTower O C L] [Algebra.IsSeparable K L]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (𝔓 : Ideal (AdicCompletion 𝔫 C)) [𝔓.IsPrime] (h𝔓 : ¬ 𝔓.IsMaximal) :
    IsField (Localization.AtPrime 𝔓) := by sorry
