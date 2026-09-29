-- Prove2me | Theorems.Thm_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
-- name    : AdicCompletion.isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/3ee0b0c1-1988-517a-8cde-85b4f09bbfe3
-- title:
--   Regularity of widehatC_𝔭 at non-maximal primes containing s
-- statement:
--   Let $O$ be a commutative ring which is a regular local ring, let $\varpi, s \in O$ be elements with $\mathfrak m_O = (\varpi, s)$, and suppose $\operatorname{ringKrullDim} O = 2$. Let $e$ be a positive natural number whose image in $O$ is a unit. Let $C$ be an integrally closed integral domain which is an $O$-algebra, module-finite over $O$ and such that $O \to C$ is injective (faithful scalar action). Let $G$ be a finite group acting on $C$ by ring automorphisms, faithfully and commuting with the $O$-action, with $O$ the ring of $G$-invariants of $C$ in the sense of `Algebra.IsInvariant`. Let $\mathfrak n$ be a maximal ideal of $C$ lying over $\mathfrak m_O$, and assume the inertia group $\mathfrak n.\mathrm{inertia}\ G$, regarded as a subgroup of the stabiliser of $\mathfrak n$ in $G$, has cardinality exactly $e$. Finally let $\mathfrak p$ be a prime ideal of the $\mathfrak n$-adic completion $\widehat{C} =$ `AdicCompletion 𝔫 C` which is not maximal and which contains the image of $s$ under $O \to \widehat{C}$. The conclusion is that the localisation $\widehat{C}_{\mathfrak p}$ is a regular local ring.
--
--   This is the regularity (indeed discrete valuation ring) statement at the non-maximal primes of the completed tame cover which lie over the branch divisor $s = 0$; it is one half of the verification that $\widehat{C}$ is regular in codimension one, and it feeds into [`AdicCompletion.isRegularLocalRing_localization_atPrime_of_not_isMaximal_of_tame`](thm.html#AdicCompletion.isRegularLocalRing_localization_atPrime_of_not_isMaximal_of_tame), where the hypothesis that $\mathfrak p$ contains $s$ is removed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
    {O : Type} [CommRing O] [IsRegularLocalRing O]
    (ϖ s : O) (hmaxO : maximalIdeal O = Ideal.span {ϖ, s}) (hdimO : ringKrullDim O = 2)
    (e : ℕ) (he : 0 < e) (heO : IsUnit (e : O))
    {C : Type} [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = e)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal)
    (hs𝔭 : algebraMap O (AdicCompletion 𝔫 C) s ∈ 𝔭) :
    IsRegularLocalRing (Localization.AtPrime 𝔭) := by sorry
