-- Prove2me | Theorems.Thm_CohCarrier_jDeg_diamondRaw_comm
-- name    : CohCarrier.jDeg_diamondRaw_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/b6630fda-cb05-547e-bcfa-54f876ce05c4
-- title:
--   Degeneracy pushforward commutes with diamond conjugation
-- statement:
--   Fix natural numbers $M$, $M'$, a subgroup $H \le (\mathbb{Z}/M)^\times$, a subgroup $H' \le (\mathbb{Z}/M')^\times$, a natural number $d$ with $d \ne 0$, $M' \ne 0$, and an additive commutative group $A$. Here $H^1(M,H;A)$ denotes the group of additive homomorphisms from the additivisation of $\Gamma_H(M)$ to $A$, where $\Gamma_H(M) \le \mathrm{SL}_2(\mathbb{Z})$ is the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the unit character `gamma0Units` on $\Gamma_0(M)$. Let $\sigma \in \Gamma_0(M)$ be such that its underlying matrix also lies in $\Gamma_0(M')$, let $h$ be a datum `LevelLE M M' H H' d`, i.e. $M \mid M'$, $d \mid M'/M$ and reduction $(\mathbb{Z}/M')^\times \to (\mathbb{Z}/M)^\times$ carries $H'$ into $H$, and let $\varphi \in H^1(M',H';A)$. Writing `diamondRaw` for precomposition with the conjugation $\gamma \mapsto \sigma\gamma\sigma^{-1}$ on the relevant $\Gamma_H$, and `jDeg` for the map sending $\varphi$ to the transfer (corestriction) to the additivisation of $\Gamma_H(M)$ of the homomorphism obtained by transporting $\varphi$ along the inverse of the isomorphism induced by the injection `iotaDeg` onto its finite-index range in $\Gamma_H(M)$, the assertion is $$\mathrm{diamondRaw}_{M,H}(\sigma)\bigl(\mathrm{jDeg}(\varphi)\bigr) = \mathrm{jDeg}\bigl(\mathrm{diamondRaw}_{M',H'}(\sigma)(\varphi)\bigr),$$ with $\sigma$ regarded on the right as an element of $\Gamma_0(M')$ via the hypothesis on its matrix. No primality or coprimality of $M$, $M'$, $d$ is assumed.
--
--   This is the compatibility of the degeneracy (trace) pushforward between cohomology carriers at levels $M'$ and $M$ with the diamond operators given by conjugation, in the form needed when the same matrix $\sigma$ lies in both $\Gamma_0(M)$ and $\Gamma_0(M')$. It is used in the level-change analysis of the corner submodules and corner ring, for instance in the results on `cornerSubmodule` and on homomorphisms out of the corner ring at an auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_jDeg_diamondRaw_comm.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.jDeg_diamondRaw_comm {M M' : ℕ} {H : Subgroup (ZMod M)ˣ}
    {H' : Subgroup (ZMod M')ˣ} {d : ℕ} {A : Type} [AddCommGroup A] [NeZero d] [NeZero M']
    (σ : Gamma0 M) (hσ' : (σ : SL(2, ℤ)) ∈ Gamma0 M') (h : LevelLE M M' H H' d)
    (φ : H1 M' H' A) :
    diamondRaw M H A σ (jDeg M M' H H' d A h φ)
      = jDeg M M' H H' d A h (diamondRaw M' H' A ⟨↑σ, hσ'⟩ φ) := by sorry
