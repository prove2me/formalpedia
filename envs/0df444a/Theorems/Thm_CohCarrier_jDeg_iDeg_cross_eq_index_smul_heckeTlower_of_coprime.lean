-- Prove2me | Theorems.Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime
-- name    : CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6d2cc5b7-8c31-5c28-9ee6-bd72a224b922
-- title:
--   Degeneracy cross-composition as an index multiple of T_q^∨
-- statement:
--   Fix naturals $M, q, M', d, d'$, all nonzero, a subgroup $H \le (\mathbb{Z}/M)^\times$, a subgroup $H' \le (\mathbb{Z}/M')^\times$ and an additive commutative group $A$. Here $\Gamma_H(M) =$ `GammaH M H` is the subgroup of $SL(2,\mathbb{Z})$ obtained by pushing the preimage of $H$ under the units map on $\Gamma_0(M)$ into $SL(2,\mathbb{Z})$, and `H1 M H A` is the group of additive homomorphisms from $\Gamma_H(M)$, written additively, to $A$. Assume $q$ and $M$ are coprime, that `LevelLE M M' H H' d` and `LevelLE M M' H H' d'` hold (each asserting $M \mid M'$, that the degree divides $M'/M$, and that the reduction map $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$ carries $H'$ into $H$), that $dq \mid M'$ as integers, and that $d' = dq$. Then, for every $\varphi \in$ `H1 M H A`, the corestriction `jDeg` in degree $d$ — the transfer to $\Gamma_H(M)$ of the character of the image of $\iota_d =$ `iotaDeg M M' H H' d h` obtained by transporting along the isomorphism of $\Gamma_{H'}(M')$ with that image — applied to the pullback `iDeg'` of $\varphi$ along $\iota_{d'}$, equals the index of the image of $\iota_d$ inside $\Gamma_H(M) \cap \Gamma_0(qM)$ (as a subgroup of the latter) times `heckeTlower M H q A φ`, the transfer to $\Gamma_H(M)$ of $\varphi$ composed with `conjLowerL M H q`, i.e. with $\gamma \mapsto$ `conjLowerMat q γ`.
--
--   This is the degeneracy-map compatibility identity: composing the pullback along the degree-$d'$ degeneracy map with the corestriction along the degree-$d$ one produces the lower Hecke operator $T_q^\vee$ up to an explicit index factor, with $q$ only required to be coprime to $M$ rather than prime. It is used in the corner case for a prime square, [`CohCarrier.jDeg_iDeg_corner_of_prime_sq`](thm.html#CohCarrier.jDeg_iDeg_corner_of_prime_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime.lean

import Definitions.Def_CohCarrier_Lower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.jDeg_iDeg_cross_eq_index_smul_heckeTlower_of_coprime {M : ℕ} {H : Subgroup (ZMod M)ˣ}
    {q : ℕ} {A : Type} [AddCommGroup A] {M' d d' : ℕ} {H' : Subgroup (ZMod M')ˣ}
    [NeZero M] [NeZero q] [NeZero d] [NeZero d'] [NeZero M']
    (hcop : Nat.Coprime q M)
    (h : LevelLE M M' H H' d) (h' : LevelLE M M' H H' d')
    (hdqM' : ((d * q : ℕ) : ℤ) ∣ (M' : ℤ)) (hdiv : d' = d * q) (φ : H1 M H A) :
    jDeg M M' H H' d A h (iDeg' M M' H H' d' A h' φ)
      = ((iotaDeg M M' H H' d h).range.subgroupOf (GammaHLower M H q)).index
          • heckeTlower M H q A φ := by sorry
