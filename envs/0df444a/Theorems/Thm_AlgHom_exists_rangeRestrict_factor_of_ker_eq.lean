-- Prove2me | Theorems.Thm_AlgHom_exists_rangeRestrict_factor_of_ker_eq
-- name    : AlgHom.exists_rangeRestrict_factor_of_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/8b15e130-26a9-5f2e-b460-f3e26a824540
-- title:
--   Equal kernels: both A-algebra maps factor through φ₁(B)
-- statement:
--   Let $A$, $B$, $K$ be commutative rings with $B$ and $K$ given as $A$-algebras, and let $\varphi_1,\varphi_2 \colon B \to K$ be $A$-algebra homomorphisms whose underlying ring homomorphisms have the same kernel, $\ker\varphi_1 = \ker\varphi_2$ as ideals of $B$. The assertion is the existence of an $A$-algebra homomorphism $\psi \colon B \to \varphi_1.\mathrm{range}$, where $\varphi_1.\mathrm{range}$ denotes the image subalgebra of $\varphi_1$ regarded as an $A$-algebra in its own right, together with an $A$-algebra homomorphism $\kappa_2 \colon \varphi_1.\mathrm{range} \to K$, such that: $\psi$ is surjective; $\kappa_2$ is injective; for every $b \in B$ the element $\psi(b)$, viewed in $K$ through the inclusion of the image subalgebra, equals $\varphi_1(b)$; and for every $b \in B$ one has $\kappa_2(\psi(b)) = \varphi_2(b)$. Thus $\varphi_1$ is the corestriction $\psi$ followed by the inclusion $\varphi_1(B) \subseteq K$, and $\varphi_2$ is $\psi$ followed by an embedding $\kappa_2$ of $\varphi_1(B)$ into $K$; the two factorisations are stated pointwise rather than as equalities of homomorphisms.
--
--   This is the first isomorphism theorem for commutative $A$-algebras in the form needed when two homomorphisms share a kernel: both are induced from a single surjection onto $\varphi_1(B)$ by two embeddings of that image into $K$. It is used by [`ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_eq_act_mapRing_of_ker_classify_eq), where two $K$-valued points of a moduli ring with the same kernel — i.e. lying over the same point of the spectrum — are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgHom_exists_rangeRestrict_factor_of_ker_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgHom.exists_rangeRestrict_factor_of_ker_eq
    {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing K] [Algebra A K]
    (φ₁ φ₂ : B →ₐ[A] K) (h : RingHom.ker φ₁.toRingHom = RingHom.ker φ₂.toRingHom) :
    ∃ (ψ : B →ₐ[A] ↥φ₁.range) (κ₂ : ↥φ₁.range →ₐ[A] K),
      Function.Surjective ψ ∧ Function.Injective κ₂ ∧
      (∀ b : B, ((ψ b : ↥φ₁.range) : K) = φ₁ b) ∧ (∀ b : B, κ₂ (ψ b) = φ₂ b) := by sorry
