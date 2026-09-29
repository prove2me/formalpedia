-- Prove2me | Theorems.Thm_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul
-- name    : Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/31b12135-3818-5960-9271-1e03b47c3a6a
-- title:
--   Algebra maps multiplicative on points are bialgebra maps
-- statement:
--   Let $R$ be a commutative ring and let $H$ and $B$ be commutative rings that are $R$-bialgebras, all three types lying in the same universe. Let $\psi \colon H \to B$ be a homomorphism of $R$-algebras. Assume two hypotheses, both quantified over all commutative rings $T$ equipped with an $R$-algebra structure and again in that universe, expressed through Mathlib's convolution monoid structure on algebra homomorphisms out of a bialgebra (the type synonym `WithConv`, whose multiplication sends $\chi, \chi'$ to the convolution $(\chi \otimes \chi')$ followed by comultiplication and multiplication, and whose unit is the counit followed by the structure map $R \to T$): first, for all $\chi, \chi' \colon B \to_{R\text{-alg}} T$, the composite $(\chi * \chi') \circ \psi$ equals, in $\mathrm{Hom}_{R\text{-alg}}(H,T)$ with convolution, the convolution product of $\chi \circ \psi$ and $\chi' \circ \psi$; second, the composite of the convolution unit of $\mathrm{Hom}_{R\text{-alg}}(B,T)$ with $\psi$ is the convolution unit of $\mathrm{Hom}_{R\text{-alg}}(H,T)$. The conclusion is that there exists an $R$-bialgebra homomorphism $\psi' \colon H \to_{R} B$ whose underlying $R$-algebra homomorphism is exactly $\psi$.
--
--   This is the Yoneda-style statement that a morphism of affine schemes which is multiplicative and unital on $T$-valued points for every test algebra $T$ comes from a morphism of bialgebras, i.e. that the functor of points determines the comultiplication and counit. It is used as a bridge between points-level computations and bialgebra-level statements, notably in the construction of lifts of multiplicative maps on split tori over henselian local rings and in the treatment of Hecke operators on the bialgebra attached to a modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Bialgebra_exists_bialgHom_coe_eq_of_comp_convMul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Bialgebra.exists_bialgHom_coe_eq_of_comp_convMul
    {R : Type u} [CommRing R] {H B : Type u} [CommRing H] [Bialgebra R H] [CommRing B] [Bialgebra R B]
    (ψ : H →ₐ[R] B)
    (hmul : ∀ (T : Type u) [CommRing T] [Algebra R T] (χ χ' : WithConv (B →ₐ[R] T)),
      WithConv.toConv ((χ * χ').ofConv.comp ψ) = WithConv.toConv (χ.ofConv.comp ψ) * WithConv.toConv (χ'.ofConv.comp ψ))
    (hone : ∀ (T : Type u) [CommRing T] [Algebra R T],
      WithConv.toConv ((1 : WithConv (B →ₐ[R] T)).ofConv.comp ψ) = (1 : WithConv (H →ₐ[R] T))) :
    ∃ ψ' : H →ₐc[R] B, (ψ' : H →ₐ[R] B) = ψ := by sorry
