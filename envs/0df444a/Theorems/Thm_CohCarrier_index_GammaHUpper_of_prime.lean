-- Prove2me | Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
-- name    : CohCarrier.index_GammaHUpper_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/5becced6-4deb-5533-8394-cbe60afb07bd
-- title:
--   Index ℓ+1 for Γ_H(M)∩Γ⁰(ℓ)
-- statement:
--   Let $M$ be a natural number and $H$ a subgroup of $(\mathbb{Z}/M\mathbb{Z})^{\times}$, and write $\Gamma_H(M)$ for the subgroup `GammaH M H` of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image, under the inclusion of $\Gamma_0(M)$ into $\mathrm{SL}_2(\mathbb{Z})$, of the preimage of $H$ under the homomorphism `gamma0Units M` from $\Gamma_0(M)$ to $(\mathbb{Z}/M\mathbb{Z})^{\times}$. Let $\ell$ be a nonzero natural number which is prime and which does not divide $M$. The subgroup `GammaHUpper M H ℓ` of the group $\Gamma_H(M)$ is defined as the pullback to $\Gamma_H(M)$ of `Gamma0Upper ℓ`, the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those matrices whose upper right entry $g_{01}$ reduces to $0$ in $\mathbb{Z}/\ell\mathbb{Z}$; that is, it consists of the elements of $\Gamma_H(M)$ whose upper right entry is divisible by $\ell$. The assertion is that this subgroup has index exactly $\ell + 1$ in $\Gamma_H(M)$.
--
--   This is the standard index computation for the level structure at a prime $\ell$ prime to $M$: the $\ell+1$ cosets correspond to the $\ell+1$ lines in $\mathbb{P}^1(\mathbb{F}_\ell)$, and the count underlies the construction of the Hecke operator $T_\ell$ on the cohomology of $\Gamma_H(M)$. It is used by the results that establish the Hecke and Atkin–Lehner relations and the eigensystem statements for this cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_index_GammaHUpper_of_prime.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.index_GammaHUpper_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    (GammaHUpper M H ℓ).index = ℓ + 1 := by sorry
