-- Prove2me | Theorems.Thm_BialgHom_exists_comp_eq_of_natural_of_map_mul
-- name    : BialgHom.exists_comp_eq_of_natural_of_map_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/38f34dfe-1b15-5b73-a00c-8c288f23c8c6
-- title:
--   Natural convolution-multiplicative transformations of points come from bialgebra maps
-- statement:
--   Let $R$ be a commutative ring and let $H_1,H_2$ be commutative rings carrying $R$-bialgebra structures. Suppose given, for every commutative $R$-algebra $T$ (with $T$ in the same universe as $H_1,H_2$), a map $\eta_T$ from $\operatorname{Hom}_{R\text{-alg}}(H_1,T)$ to $\operatorname{Hom}_{R\text{-alg}}(H_2,T)$, where both sides are taken in the type synonym `WithConv` carrying the convolution monoid structure, subject to three hypotheses: naturality, namely for all commutative $R$-algebras $T,T'$, every $R$-algebra map $g\colon T\to T'$ and every $\varphi\colon H_1\to T$ one has $\eta_{T'}(g\circ\varphi)=g\circ\eta_T(\varphi)$; multiplicativity, namely $\eta_T(\varphi\psi)=\eta_T(\varphi)\,\eta_T(\psi)$ for all $\varphi,\psi$, the products being convolution; and unitality, $\eta_T(1)=1$, the unit being the composite of the counit with the structure map of $T$. The conclusion asserts the existence of a bialgebra homomorphism $r\colon H_2\to H_1$ over $R$ such that for every such $T$ and every $\varphi\colon H_1\to T$ the underlying algebra map satisfies $\eta_T(\varphi)=\varphi\circ r$.
--
--   This is the Yoneda lemma for affine monoid schemes over $R$: a morphism of the functors of points $T\mapsto\operatorname{Hom}_{R\text{-alg}}(H_i,T)$ that is multiplicative for the convolution (monoid) structure is induced by a bialgebra homomorphism in the opposite direction. It is used in the construction of finite flat models of torsion in modular curves with prescribed Hecke and Frobenius–Verschiebung behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BialgHom_exists_comp_eq_of_natural_of_map_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem BialgHom.exists_comp_eq_of_natural_of_map_mul
    {R : Type u} [CommRing R] {H₁ H₂ : Type v} [CommRing H₁] [Bialgebra R H₁] [CommRing H₂] [Bialgebra R H₂]
    (η : ∀ (T : Type v) [CommRing T] [Algebra R T], WithConv (H₁ →ₐ[R] T) → WithConv (H₂ →ₐ[R] T))
    (hη : ∀ (T T' : Type v) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T'] (g : T →ₐ[R] T')
      (φ : WithConv (H₁ →ₐ[R] T)),
      WithConv.ofConv (η T' (WithConv.toConv (g.comp (WithConv.ofConv φ)))) = g.comp (WithConv.ofConv (η T φ)))
    (hmul : ∀ (T : Type v) [CommRing T] [Algebra R T] (φ ψ : WithConv (H₁ →ₐ[R] T)), η T (φ * ψ) = η T φ * η T ψ)
    (hone : ∀ (T : Type v) [CommRing T] [Algebra R T], η T 1 = 1) :
    ∃ r : H₂ →ₐc[R] H₁, ∀ (T : Type v) [CommRing T] [Algebra R T] (φ : WithConv (H₁ →ₐ[R] T)),
      WithConv.ofConv (η T φ) = (WithConv.ofConv φ).comp (r : H₂ →ₐ[R] H₁) := by sorry
