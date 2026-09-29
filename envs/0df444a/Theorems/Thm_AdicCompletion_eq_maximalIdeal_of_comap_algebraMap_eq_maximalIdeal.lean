-- Prove2me | Theorems.Thm_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
-- name    : AdicCompletion.eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/ad856d6e-3759-5e36-adf1-b6c8d4647ef2
-- title:
--   Primes of ̂ R contracting to 𝔪
-- statement:
--   Let $R$ be a commutative ring in the universe `Type` which is local and Noetherian, with maximal ideal $\mathfrak m =$ `maximalIdeal R`, and let $\hat R =$ `AdicCompletion (maximalIdeal R) R` be its $\mathfrak m$-adic completion, regarded as an $R$-algebra via the canonical map $R \to \hat R$. Let $P$ be an ideal of $\hat R$ which is prime. Assume that the contraction of $P$ along the structure morphism $R \to \hat R$, that is $\mathrm{comap}$ of $P$ under `algebraMap R (AdicCompletion (maximalIdeal R) R)`, is exactly the maximal ideal $\mathfrak m$ of $R$. The conclusion is that $P$ coincides with the maximal ideal of the local ring $\hat R$, the local-ring structure on the $\mathfrak m$-adic completion of a Noetherian local ring being the one provided by the project's development of adic completions of local rings.
--
--   This is the standard fact that the $\mathfrak m$-adic completion of a Noetherian local ring has a unique prime lying over $\mathfrak m$, used in its contrapositive form: a prime of $\hat R$ different from the maximal ideal contracts to a strictly smaller prime of $R$. It is invoked in the analysis of Drinfeld charts on modular curves, where completed local rings of the curve are compared with chart algebras through cyclotomic base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AdicCompletion_eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal.lean

import Mathlib
import Definitions.Def_AdicCompletionLocalRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem AdicCompletion.eq_maximalIdeal_of_comap_algebraMap_eq_maximalIdeal
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal (AdicCompletion (maximalIdeal R) R)) [P.IsPrime]
    (hP : Ideal.comap (algebraMap R (AdicCompletion (maximalIdeal R) R)) P = maximalIdeal R) :
    P = maximalIdeal (AdicCompletion (maximalIdeal R) R) := by sorry
