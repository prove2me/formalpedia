-- Prove2me | Theorems.Thm_CohCarrier_jDeg_heckeT_comm_of_dvd
-- name    : CohCarrier.jDeg_heckeT_comm_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/a55a0a9e-b5ab-5c20-95cf-19b6ef0c9ddd
-- title:
--   U_ℓ commutes with the level trace map
-- statement:
--   Let $M$ and $\ell$ be positive integers with $\ell \mid M$, let $H, H'$ be subgroups of $(\mathbb{Z}/M\mathbb{Z})^\times$, and let $A$ be an abelian group. Assume `LevelLE M M H H' 1`, i.e. $M \mid M$, $1 \mid M/M$, and every $u \in H'$ has image in $H$ under the reduction map `ZMod.unitsMap` attached to $M \mid M$; thus $H'$ is contained in $H$. Here $H^1$ at level $M$ with group $H$ is the group `H1 M H A` of additive homomorphisms $\mathrm{Additive}\,\Gamma_H(M) \to A$, where $\Gamma_H(M) =$ `GammaH M H` is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the matrices of $\Gamma_0(M)$ whose invariant under `gamma0Units M` lies in $H$; `heckeT M H ℓ A` is the endomorphism of `H1 M H A` sending $\psi$ to the transfer, along the finite-index subgroup `GammaHUpper M H ℓ` of $\Gamma_H(M)$, of the composite of the conjugation homomorphism `conjL M H ℓ` with $\psi$; and `jDeg M M H H' 1 A h` is the map `H1 M H' A → H1 M H A` given by transporting $\varphi$ along the isomorphism of $\Gamma_{H'}(M)$ with the range of `iotaDeg M M H H' 1` and then taking the transfer of the resulting character to $\Gamma_H(M)$. The assertion is that for every $\varphi \in$ `H1 M H' A` one has `heckeT M H ℓ A (jDeg … φ) = jDeg … (heckeT M H' ℓ A φ)`, i.e. the Hecke operator at $\ell$ commutes with this trace map between the two levels.
--
--   Since $\ell$ divides $M$, the operator `heckeT` at $\ell$ is the operator usually written $U_\ell$, and the statement is the $U_\ell$-equivariance of the corestriction (trace) map from the cohomology of $\Gamma_{H'}(M)$ to that of $\Gamma_H(M)$ for $H' \subseteq H$; together with the corresponding commutations at primes not dividing the level and for the diamond operators it makes this trace map a morphism of Hecke modules. It is used by [`CohCarrier.map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily`](thm.html#CohCarrier.map_jDegL_one_cornerSubmodule_eq_and_exists_algHom_cornerRing_subfamily) and by [`CuspForm.TWLevel.exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span`](thm.html#CuspForm.TWLevel.exists_linearMap_ML_HQ_HR_surjective_and_ker_eq_span) in the comparison of Hecke actions across the auxiliary levels of the patching argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_heckeT_comm_of_dvd.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDeg_heckeT_comm_of_dvd {M : ℕ} {H H' : Subgroup (ZMod M)ˣ} {ℓ : ℕ}
    {A : Type} [AddCommGroup A] [NeZero M] [NeZero ℓ]
    (h : LevelLE M M H H' 1) (hℓM : ℓ ∣ M) (φ : H1 M H' A) :
    heckeT M H ℓ A (jDeg M M H H' 1 A h φ) = jDeg M M H H' 1 A h (heckeT M H' ℓ A φ) := by sorry
