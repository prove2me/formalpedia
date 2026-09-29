-- Prove2me | Theorems.Thm_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver
-- name    : AdicCompletion.mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/03262208-7676-50f8-8ce0-96a7a98428c9
-- title:
--   Nonzerodivisors persist in the completed module-finite cover
-- statement:
--   Let $O$ be a commutative Noetherian local ring with maximal ideal $\mathfrak m = \mathrm{maximalIdeal}\,O$, and let $C$ be a commutative ring which is an integral domain, equipped with an $O$-algebra structure that makes it a finite $O$-module and for which the scalar action is faithful (equivalently, the structure map $O \to C$ is injective). Let $\mathfrak n$ be an ideal of $C$ which is maximal and lies over $\mathfrak m$, i.e. $\mathfrak n \cap O$, the contraction of $\mathfrak n$ along the structure map, equals $\mathfrak m$. Form the $\mathfrak m$-adic completion $\widehat O$ of $O$ and the $\mathfrak n$-adic completion $\widehat{C}_{\mathfrak n}$ of $C$, the latter an algebra over the former. The assertion is that the structure map $\widehat O \to \widehat{C}_{\mathfrak n}$ carries nonzerodivisors to nonzerodivisors: for every $r \in \widehat O$ lying in the multiplicative submonoid of nonzerodivisors of $\widehat O$, its image $\mathrm{algebraMap}\,r$ lies in the submonoid of nonzerodivisors of $\widehat{C}_{\mathfrak n}$. Note that $O$ itself is not assumed to be a domain, nor is $\widehat{C}_{\mathfrak n}$ asserted to be one.
--
--   This is the torsion-freeness statement for the completed module-finite cover: $\widehat{C}_{\mathfrak n}$ contains no element killed by a nonzerodivisor of the completed base $\widehat O$, in exactly the form needed to pass from $\widehat O$-regular elements to $\widehat{C}_{\mathfrak n}$-regular ones. It is used in the analysis of the local rings of $\widehat{C}_{\mathfrak n}$ at its primes, for instance in the statements that suitable localisations at primes are fields, are regular local, or are normal domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver.lean

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open scoped AdicCompletion.GaloisAction

theorem AdicCompletion.mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
    ∀ r : AdicCompletion (maximalIdeal O) O, r ∈ nonZeroDivisors (AdicCompletion (maximalIdeal O) O) →
      algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) r ∈ nonZeroDivisors (AdicCompletion 𝔫 C) := by sorry
