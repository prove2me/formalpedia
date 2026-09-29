-- Prove2me | Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm
-- name    : CohCarrier.heckeT_diamondRaw_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/6a9816b7-7fa0-5171-a59b-f229f3034ead
-- title:
--   Hecke T_ℓ commutes with the raw diamond action
-- statement:
--   Fix $M \in \mathbb{N}$, a subgroup $H \le (\mathbb{Z}/M\mathbb{Z})^{\times}$, and $\ell \in \mathbb{N}$ with $\ell \neq 0$. Let $\Gamma_H(M) \le \mathrm{SL}(2,\mathbb{Z})$ be `GammaH M H`, the image under the inclusion $\Gamma_0(M) \hookrightarrow \mathrm{SL}(2,\mathbb{Z})$ of the preimage of $H$ under the character $\Gamma_0(M) \to (\mathbb{Z}/M\mathbb{Z})^{\times}$ given by `gamma0Units M`. Let $\sigma \in \Gamma_0(M)$ and assume that $\ell M$, viewed in $\mathbb{Z}$, divides the lower-left entry of $\sigma$ as a matrix in $\mathrm{SL}(2,\mathbb{Z})$. Let $V$ be an abelian group (in the base universe) and let $F$ be an element of `H1 M H V`, that is, a homomorphism from $\Gamma_H(M)$, written additively, to $V$. Two additive endomorphisms of `H1 M H V` are in play: `diamondRaw M H V σ`, precomposition with the conjugation $\gamma \mapsto \sigma \gamma \sigma^{-1}$ of $\Gamma_H(M)$; and `heckeT M H ℓ V`, which sends a homomorphism to the group-theoretic transfer, from $\Gamma_H(M)$ to its subgroup `GammaHUpper M H ℓ`, of the composite of that homomorphism with `conjL M H ℓ`, the map `GammaHUpper M H ℓ` $\to \Gamma_H(M)$ given by conjugation by the upper-triangular matrix `conjUpperMat ℓ`. The assertion is that the two operators commute on $F$: applying `heckeT M H ℓ V` to `diamondRaw M H V σ F` gives the same homomorphism as applying `diamondRaw M H V σ` to `heckeT M H ℓ V F`.
--
--   This is the commutation of the Hecke operator $T_\ell$ with the diamond (conjugation) action on the $V$-valued cohomology carrier $\mathrm{Hom}(\Gamma_H(M), V)$, in the transfer-theoretic presentation of $T_\ell$; the divisibility condition $\ell M \mid c(\sigma)$ is what makes conjugation by $\sigma$ compatible with the chosen coset data at $\ell$. It is used when Hecke and diamond operators must be treated as a single commuting family, for instance in the decomposition statements for invariant submodules of the Hecke action and in the construction of Galois modules from parabolic homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_heckeT_diamondRaw_comm.lean

import Definitions.Def_CohCarrier_Level

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.heckeT_diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (diamondRaw M H V σ F) = diamondRaw M H V σ (heckeT M H ℓ V F) := by sorry
