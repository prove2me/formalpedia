-- Prove2me | Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
-- name    : CohCarrier.iDeg_heckeT_comm_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/36484395-36bf-5375-b50d-6c0789e4417e
-- title:
--   Degeneracy pullback commutes with T_ℓ at coprime ℓ
-- statement:
--   Fix natural numbers $M, M'$, subgroups $H \le (\mathbb{Z}/M)^\times$ and $H' \le (\mathbb{Z}/M')^\times$, natural numbers $d, \ell$ both nonzero, and an additive abelian group $A$. Here `H1 M H A` denotes the group of homomorphisms from $\Gamma_H(M)$ to $A$, where $\Gamma_H(M) \le \mathrm{SL}(2,\mathbb{Z})$ is the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ of the preimage of $H$ under the reduction-of-diagonal map `gamma0Units M`. Assume a level datum $h$ : `LevelLE M M' H H' d`, i.e. $M \mid M'$, $d \mid M'/M$, and every $u \in H'$ reduces into $H$ under $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$; assume further that $\ell$ is coprime to $d$, that $\ell$ is prime, and that $\ell \nmid M'$. Then for every $\varphi : \Gamma_H(M) \to A$ the two composites agree: applying the Hecke operator `heckeT` at level $(M,H)$ — the transfer of $\varphi$ restricted along the conjugation map $\Gamma_H^{\mathrm{up}}(M,\ell) \to \Gamma_H(M)$ given by `conjL` — and then pulling back along the degeneracy homomorphism `iotaDeg` $: \Gamma_{H'}(M') \to \Gamma_H(M)$, $\gamma \mapsto$ `conjLowerMat d` $\gamma$, gives the same homomorphism $\Gamma_{H'}(M') \to A$ as first pulling back along `iotaDeg` and then applying `heckeT` at level $(M',H')$.
--
--   This is the standard compatibility of the degeneracy (level-change) maps with the Hecke operator $T_\ell$ at a prime $\ell$ coprime to the degeneracy index $d$ and to the higher level $M'$, here in the group-cohomological incarnation where $T_\ell$ is realised as a transfer map and the degeneracy map as precomposition with a conjugated inclusion of congruence subgroups. It is used throughout the comparison of Hecke modules at different levels, in particular in the analysis of corner submodules and of eigensystems on $H^1$ that feeds the level-lowering arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_iDeg_heckeT_comm_of_coprime.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.iDeg_heckeT_comm_of_coprime {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    {d ℓ : ℕ} {A : Type} [AddCommGroup A] [NeZero d] [NeZero ℓ] (h : LevelLE M M' H H' d)
    (hℓd : Nat.Coprime ℓ d) (hℓ : ℓ.Prime) (hℓM' : ¬ ℓ ∣ M') (φ : H1 M H A) :
    iDeg' M M' H H' d A h (heckeT M H ℓ A φ) = heckeT M' H' ℓ A (iDeg' M M' H H' d A h φ) := by sorry
