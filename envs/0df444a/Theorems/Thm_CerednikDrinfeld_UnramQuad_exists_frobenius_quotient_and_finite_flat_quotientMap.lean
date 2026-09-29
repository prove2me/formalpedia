-- Prove2me | Theorems.Thm_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap
-- name    : CerednikDrinfeld.UnramQuad.exists_frobenius_quotient_and_finite_flat_quotientMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/670400cd-9e58-583d-b487-7efc3c6ebecc
-- title:
--   Frobenius involution and finite flatness modulo πⁿ⁺¹
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi \in \mathcal O$, and let $O^{\mathrm{nr}}$ be a commutative $\mathcal O$-algebra equipped with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$. Write $\mathcal O_2 := \mathrm{Eq}(\mathrm{Fr} \circ \mathrm{Fr}, \mathrm{id})$ for the $\mathcal O$-subalgebra of $O^{\mathrm{nr}}$ on which the square $\mathrm{Fr}\circ\mathrm{Fr}$, viewed as an $\mathcal O$-algebra map, agrees with the identity. Assume $\mathcal O_2$ is free as an $\mathcal O$-module and that $\operatorname{finrank}_{\mathcal O} \mathcal O_2 = 2$. Then there exists a family of $\mathcal O$-algebra automorphisms $\mathrm{Fr}_2(n)$ of the quotient $\mathcal O_2 / (\,(\pi \cdot 1_{\mathcal O_2})^{n+1}\,)$, indexed by $n \in \mathbb N$, with the following three properties. First, $\mathrm{Fr}_2(n)$ is induced by $\mathrm{Fr}$: for all $y, y' \in \mathcal O_2$ whose images in $O^{\mathrm{nr}}$ satisfy $y' = \mathrm{Fr}(y)$, one has $\mathrm{Fr}_2(n)(\bar y) = \bar{y'}$. Second, each $\mathrm{Fr}_2(n)$ is an involution: $\mathrm{Fr}_2(n)(\mathrm{Fr}_2(n)(x)) = x$ for all $x$. Third, for every $n$ the ring homomorphism $\mathcal O/(\pi^{n+1}) \to \mathcal O_2/((\pi \cdot 1_{\mathcal O_2})^{n+1})$ induced by the structure map $\mathcal O \to \mathcal O_2$ is finite and flat.
--
--   This supplies the coefficient rings and their Frobenius involutions for the Čerednik–Drinfeld/Mumford construction: $\mathcal O_2$ plays the role of the quadratic unramified extension of $\mathcal O$ inside $O^{\mathrm{nr}}$, the truncations $\mathcal O_2/\pi^{n+1}$ are the bases over which the formal tower is built, and the descended involution is the Frobenius used to twist it. It is cited in the construction of the twisted Mumford tower, [`CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower`](thm.html#CerednikDrinfeld.FormalOmega.MumfordTower.exists_twistedTower).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.UnramQuad.exists_frobenius_quotient_and_finite_flat_quotientMap
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hfree : Module.Free 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
    (hrank : Module.finrank 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) = 2) :
    ∃ Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}),

      (∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
        Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') ∧

      (∀ (n : ℕ) (x : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), Fr₂ n (Fr₂ n x) = x) ∧

      (∀ n : ℕ, (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            𝒪 ⧸ Ideal.span {π ^ (n + 1)} →+* (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})).Finite ∧
        (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            𝒪 ⧸ Ideal.span {π ^ (n + 1)} →+* (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})).Flat) := by sorry
