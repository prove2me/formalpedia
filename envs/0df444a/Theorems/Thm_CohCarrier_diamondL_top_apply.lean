-- Prove2me | Theorems.Thm_CohCarrier_diamondL_top_apply
-- name    : CohCarrier.diamondL_top_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/0c615b81-bca9-50c5-acab-68a0cef64484
-- title:
--   Diamond operators act trivially at level H=top
-- statement:
--   Let $M$ be a nonzero natural number, let $\mathcal{O}$ be a commutative ring, and let $d$ be a unit of $\mathbb{Z}/M$. Here $\Gamma_H(M)$, for $H$ a subgroup of $(\mathbb{Z}/M)^\times$, is the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ obtained as the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the character `gamma0Units M` on $\Gamma_0(M)$, and [`CohCarrier.H1 M H A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms from the additive group underlying $\Gamma_H(M)$ to an abelian group $A$. For $H=\top$ the group $\Gamma_\top(M)$ is thus all of $\Gamma_0(M)$, and the statement concerns an arbitrary element $\varphi$ of [`CohCarrier.H1 M ⊤ 𝒪`](def/CohCarrier_Level.html#L162), i.e. an additive homomorphism $\Gamma_0(M)\to\mathcal{O}$. The operator [`CohCarrier.diamondL M ⊤ 𝒪 d`](def/CohCarrier_Inst.html#L55) is the $\mathcal{O}$-linear endomorphism of this module given by precomposition with conjugation by a chosen element $\sigma\in\Gamma_0(M)$ with `gamma0Units M` $\sigma=d$. The assertion is that this operator fixes $\varphi$: one has $\langle d\rangle\varphi=\varphi$ for every such $\varphi$, so the diamond operator at $H=\top$ is the identity.
--
--   This is the familiar fact that the diamond operators degenerate to the identity at full level $\Gamma_0(M)$, in the form needed for the group-cohomological carrier $\mathrm{Hom}(\Gamma_H(M),\mathcal{O})$ used in the Hecke-module computations. It is used in the analysis of the Hecke action on the $H=\top$ carrier, in particular in the construction of the ideal attached to an absolutely irreducible situation and in the dimension count for the corner submodule cut out by Hecke eigenvalue conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_diamondL_top_apply.lean

import Mathlib
import Definitions.Def_CohCarrier_Inst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CongruenceSubgroup

theorem CohCarrier.diamondL_top_apply (M : ℕ) [NeZero M] (𝒪 : Type) [CommRing 𝒪]
    (d : (ZMod M)ˣ) (φ : CohCarrier.H1 M ⊤ 𝒪) :
    CohCarrier.diamondL M ⊤ 𝒪 d φ = φ := by sorry
