-- Prove2me | Theorems.Thm_CohCarrier_index_GammaHUpper_of_dvd
-- name    : CohCarrier.index_GammaHUpper_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/e0cfcc9d-fa7f-5c3a-8221-2d044e9658ba
-- title:
--   Index ℓ of the upper-triangular subgroup of Γ_H(M)
-- statement:
--   Let $M$ be a natural number, $H$ a subgroup of $(\mathbb{Z}/M\mathbb{Z})^{\times}$, and $\ell$ a nonzero natural number dividing $M$. Write $\Gamma_H(M)$ for the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\mathrm{SL}_2(\mathbb{Z})$, namely the image under the inclusion $\Gamma_0(M)\hookrightarrow \mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the homomorphism [`CohCarrier.gamma0Units M`](def/CohCarrier_Level.html#L121) from $\Gamma_0(M)$ to $(\mathbb{Z}/M\mathbb{Z})^{\times}$ (the unit attached to a matrix of $\Gamma_0(M)$ by reduction of a diagonal entry modulo $M$). Write [`CohCarrier.Gamma0Upper`](def/CohCarrier_Level.html#L90) $\ell$ for the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those $g$ with $g_{01}\equiv 0 \pmod{\ell}$. The theorem asserts that the subgroup [`CohCarrier.GammaHUpper M H ℓ`](def/CohCarrier_Level.html#L210) of the group $\Gamma_H(M)$ cut out by that congruence, i.e. the preimage of [`CohCarrier.Gamma0Upper`](def/CohCarrier_Level.html#L90) $\ell$ in $\Gamma_H(M)$, has index exactly $\ell$ in $\Gamma_H(M)$. No primality assumption on $\ell$ is made, and the hypothesis $\ell \mid M$ is genuinely used: for $\ell$ prime to $M$ the index would be $\ell+1$.
--
--   This is the count of cosets entering the definition of the Hecke operator $U_\ell$ at a level-dividing $\ell$: the index is $\ell$ rather than $\ell+1$ because $\ell \mid M$ forces the lower-left entry of any element of $\Gamma_0(M)$ to vanish modulo $\ell$, so that no coset at infinity occurs. It is used in the project's index and degree computations for the maps between cohomology carriers, among them [`CohCarrier.index_range_iotaDeg_of_prime_sq`](thm.html#CohCarrier.index_range_iotaDeg_of_prime_sq), [`CohCarrier.jDeg_iDeg_four_identities_of_dvd`](thm.html#CohCarrier.jDeg_iDeg_four_identities_of_dvd) and [`CohCarrier.jDeg_iDeg_nine_identities_of_prime`](thm.html#CohCarrier.jDeg_iDeg_nine_identities_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_index_GammaHUpper_of_dvd.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.index_GammaHUpper_of_dvd (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ] (hℓM : ℓ ∣ M) :
    (CohCarrier.GammaHUpper M H ℓ).index = ℓ := by sorry
