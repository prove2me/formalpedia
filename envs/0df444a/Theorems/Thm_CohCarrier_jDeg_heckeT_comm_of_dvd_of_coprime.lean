-- Prove2me | Theorems.Thm_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime
-- name    : CohCarrier.jDeg_heckeT_comm_of_dvd_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/a05d38db-5ea4-566d-86d3-b073c2083d8b
-- title:
--   U_ℓ commutes with the degeneracy trace map j_d
-- statement:
--   Let $M,M'$ be natural numbers, $H$ a subgroup of $(\mathbb{Z}/M\mathbb{Z})^\times$, $H'$ a subgroup of $(\mathbb{Z}/M'\mathbb{Z})^\times$, let $d,\ell$ be natural numbers and $A$ an additive abelian group, with $d$, $M'$ and $\ell$ nonzero. Assume `LevelLE M M' H H' d`, that is: $M \mid M'$, $d \mid M'/M$, and the reduction modulo $M$ of every unit of $\mathbb{Z}/M'\mathbb{Z}$ lying in $H'$ lies in $H$. Assume further that $\ell$ is coprime to $M'/(Md)$ and that $\ell \mid M$. Here, for a level $N$ and a subgroup $K \le (\mathbb{Z}/N\mathbb{Z})^\times$, `GammaH N K` is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of those elements of $\Gamma_0(N)$ whose associated unit in $(\mathbb{Z}/N\mathbb{Z})^\times$ lies in $K$, and `H1 N K A` is the group of additive homomorphisms from the additivisation of `GammaH N K` to $A$, i.e. $\mathrm{Hom}(\Gamma_K(N), A)$. The map `jDeg` sends $\psi \in \mathrm{Hom}(\Gamma_{H'}(M'),A)$ to the transfer to $\Gamma_H(M)$, along the finite-index inclusion of the image of the injective homomorphism `iotaDeg M M' H H' d h` $\colon \Gamma_{H'}(M') \to \Gamma_H(M)$, of $\psi$ transported through the induced isomorphism onto that image; the operator `heckeT N K ℓ A` sends $\psi$ to the transfer from the subgroup `GammaHUpper N K ℓ` of $\Gamma_K(N)$ to $\Gamma_K(N)$ of the composite of $\psi$ with the homomorphism `conjL`, given by $\gamma \mapsto$ `conjUpperMat ℓ γ`. The conclusion is that for every $\varphi \in \mathrm{Hom}(\Gamma_{H'}(M'),A)$ one has `heckeT M H ℓ A (jDeg … φ) = jDeg … (heckeT M' H' ℓ A φ)`.
--
--   Since $\ell$ divides both levels, `heckeT` at $\ell$ is the operator $U_\ell$ on the relevant group cohomology in degree one, and the statement is the Atkin–Lehner style commutation of $U_\ell$ with the degeneracy trace (corestriction) map $j_d$ between levels $M'$ and $M$, valid under coprimality of $\ell$ with the complementary divisor $M'/(Md)$ rather than with $d$. It is used in the computations with the corner submodules at auxiliary level and in the comparison of Hecke modules at the Taylor–Wiles auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_heckeT_comm_of_dvd_of_coprime.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDeg_heckeT_comm_of_dvd_of_coprime {M M' : ℕ} {H : Subgroup (ZMod M)ˣ}
    {H' : Subgroup (ZMod M')ˣ} {d ℓ : ℕ} {A : Type} [AddCommGroup A] [NeZero d] [NeZero M']
    [NeZero ℓ] (h : LevelLE M M' H H' d) (hℓe : Nat.Coprime ℓ (M' / (M * d))) (hℓM : ℓ ∣ M)
    (φ : H1 M' H' A) :
    heckeT M H ℓ A (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (heckeT M' H' ℓ A φ) := by sorry
