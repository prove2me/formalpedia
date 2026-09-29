-- Prove2me | Theorems.Thm_AdicCompletion_isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime
-- name    : AdicCompletion.isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/0425789f-141d-5971-96f3-66209c6675bc
-- title:
--   Domain and normality pass to the completion of the localisation
-- statement:
--   Let $O$ be a commutative local ring, $C$ a commutative $O$-algebra, and $\mathfrak n \subseteq C$ a maximal ideal lying over the maximal ideal of $O$. Let $S$ be a commutative local ring which is a $C$-algebra realising the localisation of $C$ at the prime $\mathfrak n$, so that $S$ satisfies `IsLocalization.AtPrime S 𝔫` and its maximal ideal is the image of $\mathfrak n$. Assume that the $\mathfrak n$-adic completion $\widehat{C}_{\mathfrak n} =$ `AdicCompletion 𝔫 C`, the inverse limit of the rings $C/\mathfrak n^{k}$, is a domain and is integrally closed in its fraction field. The conclusion is the conjunction of two assertions about the adic completion of $S$ along its maximal ideal, `AdicCompletion (maximalIdeal S) S`: it is a domain, and it is integrally closed.
--
--   This is the transfer of the properties 'integrally closed domain' between the $\mathfrak n$-adic completion of $C$ and the adic completion of the local ring $C_{\mathfrak n}$, resting on the fact that completion at a maximal ideal is insensitive to localisation there. It feeds the analysis of invariants of tame actions on completed local rings, being used by [`AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame`](thm.html#AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isDomain_and_isIntegrallyClosed_adicCompletion_maximalIdeal_of_isLocalization_atPrime {O : Type} [CommRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [Algebra O C] (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (S : Type) [CommRing S] [IsLocalRing S] [Algebra C S] [IsLocalization.AtPrime S 𝔫]
    (hd : IsDomain (AdicCompletion 𝔫 C)) (hn : IsIntegrallyClosed (AdicCompletion 𝔫 C)) :
    IsDomain (AdicCompletion (maximalIdeal S) S) ∧ IsIntegrallyClosed (AdicCompletion (maximalIdeal S) S) := by sorry
