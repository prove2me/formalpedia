-- Prove2me | Theorems.Thm_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff
-- name    : CohCarrier.mem_map_iDegL_one_parabolicHoms_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/09d085dc-9358-5bce-bbfd-a19d7241a167
-- title:
--   Image of parabolic H¹(Γ₀(M)) equals diamond-invariant parabolic part
-- statement:
--   Fix a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^\times$, a commutative ring $R$ and an $R$-module $A$. Here [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) is the subgroup of $SL(2,\mathbb{Z})$ consisting of those $\gamma \in \Gamma_0(M)$ whose lower-right entry reduces into $H$, so that [`CohCarrier.GammaH M ⊤`](def/CohCarrier_Level.html#L133) is $\Gamma_0(M)$ itself, and [`CohCarrier.H1 M H A`](def/CohCarrier_Level.html#L162) is the group of additive homomorphisms from $\Gamma_H(M)$, written additively, to $A$. Assume [`CohCarrier.LevelLE M M ⊤ H 1`](def/CohCarrier_Level.html#L330), the (here automatically valid) record that $M \mid M$, $1 \mid M/M$ and every unit in $H$ reduces into $\top$, and assume that the image of the index $[(\mathbb{Z}/M\mathbb{Z})^\times : H]$ in $R$ is a unit. Let $\varphi \colon \Gamma_H(M) \to A$ be a homomorphism. Then $\varphi$ lies in the image, under the $R$-linear restriction map [`CohCarrier.iDegL`](def/CohCarrier_Level.html#L401) given by precomposition with the inclusion $\Gamma_H(M) \hookrightarrow \Gamma_0(M)$, of the submodule of homomorphisms $\Gamma_0(M) \to A$ vanishing on every element of squared trace $4$, if and only if $\varphi$ itself vanishes on every element of $\Gamma_H(M)$ of squared trace $4$ and satisfies $\varphi(\sigma \cdot \sigma^{-1}) = \varphi$ for all $\sigma \in \Gamma_0(M)$.
--
--   This identifies the $\Gamma_0(M)$-old parabolic part of $H^1(\Gamma_H(M), A)$ with trivial coefficients as the parabolic, diamond-invariant part, the invertibility of $[(\mathbb{Z}/M\mathbb{Z})^\times : H]$ in $R$ being what makes both inclusions available. It is used to transport the degeneracy-adjoint pairing on parabolic cohomology from level $\Gamma_0(M)$ to level $\Gamma_H(M)$ in the construction of the local Hecke data at a corner.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_mem_map_iDegL_one_parabolicHoms_iff.lean

import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem CohCarrier.mem_map_iDegL_one_parabolicHoms_iff
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
    (h₁ : CohCarrier.LevelLE M M ⊤ H 1) (hunit : IsUnit ((H.index : ℕ) : R)) (φ : CohCarrier.H1 M H A) :
    φ ∈ (ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M ⊤) A).map
        (CohCarrier.iDegL M M ⊤ H 1 A R h₁) ↔
      (φ ∈ ModularCurve.Period.parabolicHoms R (CohCarrier.GammaH M H) A ∧
        ∀ σ : CongruenceSubgroup.Gamma0 M, CohCarrier.diamondRaw M H A σ φ = φ) := by sorry
