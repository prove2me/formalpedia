-- Prove2me | Theorems.Thm_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver
-- name    : AdicCompletion.isLocalRing_and_ringKrullDim_le_two_of_liesOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/04dd7a69-9865-5e56-a92d-c010849b9d7f
-- title:
--   Locality and dimension ≤ 2 of the n-adic completion
-- statement:
--   Let $O$ be a commutative ring that is Noetherian and local with $\operatorname{ringKrullDim} O = 2$ (the equality taken in $\mathbb{N}\infty$ with a bottom element, so $O$ is in particular nonzero), let $C$ be a commutative ring equipped with an $O$-algebra structure making it finite as an $O$-module, and let $\mathfrak n$ be an ideal of $C$ that is maximal and lies over the maximal ideal of $O$, i.e. the preimage of $\mathfrak n$ under the structure map $O \to C$ is $\mathfrak m_O$. The conclusion is the conjunction of two assertions about the $\mathfrak n$-adic completion $\widehat{C}_{\mathfrak n} = \varprojlim_k C/\mathfrak n^k$ (formed from $C$ itself, not from a localisation): first, $\widehat{C}_{\mathfrak n}$ is a local ring; second, its Krull dimension satisfies $\operatorname{ringKrullDim} \widehat{C}_{\mathfrak n} \le 2$ as an inequality in $\mathbb{N}\infty$ with a bottom element. No normality, reducedness or flatness hypothesis on $C$ over $O$ is imposed.
--
--   This is the local-algebraic input for the study of the completed cover at a closed point: a module-finite algebra over a two-dimensional Noetherian local ring, completed at a maximal ideal above the closed point, is again local of dimension at most two. It is used in the proof that such a completion is a normal domain under the invariance and tameness hypotheses of [`AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame`](thm.html#AdicCompletion.isDomain_and_isIntegrallyClosed_of_isInvariant_of_isLocalization_atPrime_of_tame), and it rests on the fact that completing a Noetherian local ring at its maximal ideal leaves the Krull dimension unchanged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isLocalRing_and_ringKrullDim_le_two_of_liesOver.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isLocalRing_and_ringKrullDim_le_two_of_liesOver {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] (hdimO : ringKrullDim O = 2)
    {C : Type} [CommRing C] [Algebra O C] [Module.Finite O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    IsLocalRing (AdicCompletion 𝔫 C) ∧ ringKrullDim (AdicCompletion 𝔫 C) ≤ (2 : WithBot ℕ∞) := by sorry
