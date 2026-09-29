-- Prove2me | Theorems.Thm_CuspForm_Bfam_degeneracyBlock
-- name    : CuspForm.Bfam.degeneracyBlock
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1e7d5005-db50-507a-9de2-3ee64ba28799
-- title:
--   Degeneracy adjointness of the chosen pairing family B
-- statement:
--   Let $\mathcal O$ be a commutative local domain of characteristic zero and let $p$ be an odd prime that is not a unit in $\mathcal O$. For $M\ge 1$ write $\Gamma_H(M)\le SL_2(\mathbb Z)$ for `GammaH M H`, the matrices of $\Gamma_0(M)$ whose lower-right entry reduces into $H\le(\mathbb Z/M)^\times$, so that $\Gamma_\top(M)=\Gamma_0(M)$; write $H^1(M,H;\mathcal O)$ for the additive homomorphisms $\mathrm{Additive}\,\Gamma_H(M)\to\mathcal O$, let `parabolicHoms` be the submodule of those vanishing on all $\gamma$ with $\operatorname{tr}(\gamma)^2=4$, and set $W(M,H)$ to be its image under `iDegL M M ⊤ H 1`, i.e. restriction along $\Gamma_H(M)\le\Gamma_0(M)$ as encoded by a datum $h_1:$ `LevelLE M M ⊤ H 1`. The assertion is: for all nonzero $M,M'$, subgroups $H\le(\mathbb Z/M)^\times$, $H'\le(\mathbb Z/M')^\times$ with data $h_1,h_1'$, for all nonzero $d,d'$ and data $h,h':$ `LevelLE M M' H H' d`, resp. $d'$ (each recording $M\mid M'$, $d\mid M'/M$, and that reduction modulo $M$ carries $H'$ into $H$), such that $dd'=M'/M$ and $H'$ is exactly the preimage of $H$ under `ZMod.unitsMap h.dvd`, and provided $[(\mathbb Z/M)^\times:H]$ and $[(\mathbb Z/M')^\times:H']$ are units in $\mathcal O$: for $x\in W(M,H)$, $y\in W(M',H')$, and elements $ix\in W(M',H')$, $jy\in W(M,H)$ whose underlying cohomology classes satisfy $ix=$ `iDegL M M' H H' d` $x$ and $jy=$ `jDegL M M' H H' d'` $y$ (pull-back along the degeneracy map `iotaDeg`, and the transfer of the corresponding push-forward), the chosen family [`CuspForm.Bfam 𝒪`](def/CuspForm_CornerPairingFamily.html#L57) of $\mathcal O$-bilinear forms satisfies $B_{M,H}(jy,x)=B_{M',H'}(y,ix)$.
--
--   This is the degeneracy-adjointness half of the defining specification of the pairing family [`CuspForm.Bfam`](def/CuspForm_CornerPairingFamily.html#L57): the transfer $j_{d'}$ between levels $M\mid M'$ is adjoint to the pull-back $i_d$ for the chosen pairings on the parabolic parts, classically the statement that the cup-product pairing twisted by the Atkin–Lehner involution intertwines the two degeneracy maps. It is used in the Taylor–Wiles patching input, via the bijectivity and presentation results for the local Hecke algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_Bfam_degeneracyBlock.lean

import Definitions.Def_CuspForm_CornerPairingFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier

theorem CuspForm.Bfam.degeneracyBlock
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] [IsLocalRing 𝒪]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpu : ¬ IsUnit (p : 𝒪)) :
    ∀ (M M' : ℕ) [NeZero M] [NeZero M'] (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ)
        (h₁ : LevelLE M M ⊤ H 1) (h₁' : LevelLE M' M' ⊤ H' 1)
        (d d' : ℕ) [NeZero d] [NeZero d'] (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
        (hdd' : d * d' = M' / M)
        (hH' : ∀ u : (ZMod M')ˣ, u ∈ H' ↔ ZMod.unitsMap h.dvd u ∈ H),
        IsUnit ((H.index : ℕ) : 𝒪) → IsUnit ((H'.index : ℕ) : 𝒪) →
        ∀ (x : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)))
          (y : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
          (ix : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M' ⊤) 𝒪).map (iDegL M' M' ⊤ H' 1 𝒪 𝒪 h₁')))
          (jy : ↥((ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))),
        (ix : H1 M' H' 𝒪) = iDegL M M' H H' d 𝒪 𝒪 h x →
        (jy : H1 M H 𝒪) = jDegL M M' H H' d' 𝒪 𝒪 h' y →
        CuspForm.Bfam 𝒪 M H h₁ jy x = CuspForm.Bfam 𝒪 M' H' h₁' y ix := by sorry
