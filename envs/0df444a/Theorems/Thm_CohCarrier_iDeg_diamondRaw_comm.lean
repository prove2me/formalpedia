-- Prove2me | Theorems.Thm_CohCarrier_iDeg_diamondRaw_comm
-- name    : CohCarrier.iDeg_diamondRaw_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/bbab9cff-e155-50a3-8bda-6ad6e0115e34
-- title:
--   Degeneracy pullback commutes with raw diamond operators
-- statement:
--   Fix nonzero naturals $M, M'$ and $d$, subgroups $H \le (\mathbb{Z}/M)^\times$ and $H' \le (\mathbb{Z}/M')^\times$, and a witness $h$ of `LevelLE M M' H H' d`, i.e. $M \mid M'$, $d \mid M'/M$, and the reduction map $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$ carries $H'$ into $H$. Let $A$ be an additive abelian group; here $H1\,M\,H\,A$ denotes the additive homomorphisms from $\mathrm{Additive}\,\Gamma_H(M)$ to $A$, where $\Gamma_H(M) \le \mathrm{SL}(2,\mathbb{Z})$ is the image of those elements of $\Gamma_0(M)$ whose lower-right reduction lies in $H$. For a matrix $B$ with $d \mid B_{10}$, `conjLowerMat d B` is $\begin{pmatrix} B_{00} & dB_{01} \\ B_{10}/d & B_{11}\end{pmatrix}$, that is $\delta_d B \delta_d^{-1}$ with $\delta_d = \mathrm{diag}(d,1)$; precomposition with $\gamma' \mapsto$ `conjLowerMat d γ'` gives `iDeg'` $: H1\,M\,H\,A \to H1\,M'\,H'\,A$, and precomposition with $\gamma \mapsto \tau \gamma \tau^{-1}$ gives `diamondRaw` $\tau$. Given $\sigma' \in \Gamma_0(M')$ with $d \mid \sigma'_{10}$, and $\sigma \in \Gamma_0(M)$ whose underlying matrix equals `conjLowerMat d σ'`, the assertion is that for every $\varphi \in H1\,M\,H\,A$ one has `iDeg'` $(\langle\sigma\rangle\varphi) = \langle\sigma'\rangle($ `iDeg'` $\varphi)$.
--
--   This is the compatibility of the degeneracy pullback between cohomology carriers of levels $(M,H)$ and $(M',H')$ with the diamond operators, one lift being the $\delta_d$-conjugate of the other. It is used as the intertwining input for the corner-transport arguments in the treatment of Ihara's lemma, and has a transfer-side companion for the other degeneracy map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_iDeg_diamondRaw_comm.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.iDeg_diamondRaw_comm
    {M M' : ℕ} [NeZero M] [NeZero M'] {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]
    (h : LevelLE M M' H H' d) {A : Type} [AddCommGroup A] (σ' : Gamma0 M')
    (hd : (d : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0) (σ : Gamma0 M) (hσ : (σ : SL(2, ℤ)) = conjLowerMat d (σ' : SL(2, ℤ)) hd)
    (φ : H1 M H A) :
    iDeg' M M' H H' d A h (diamondRaw M H A σ φ) = diamondRaw M' H' A σ' (iDeg' M M' H H' d A h φ) := by sorry
