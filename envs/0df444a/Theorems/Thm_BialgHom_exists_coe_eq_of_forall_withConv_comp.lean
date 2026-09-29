-- Prove2me | Theorems.Thm_BialgHom_exists_coe_eq_of_forall_withConv_comp
-- name    : BialgHom.exists_coe_eq_of_forall_withConv_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6561d473-432f-5807-a999-849acbdd5dc9
-- title:
--   An algebra map multiplicative on K-points is a bialgebra map
-- statement:
--   Let $R$ be a commutative ring and $K$ a commutative $R$-algebra whose structure map $R \to K$ is injective, and let $H$, $H'$ be commutative rings carrying $R$-bialgebra structures. Let $\varphi : H \to H'$ be a homomorphism of $R$-algebras. Assume: (i) separation: an element $x \in H' \otimes_R H'$ is zero as soon as $\theta(x) = 0$ for every $R$-algebra homomorphism $\theta : H' \otimes_R H' \to K$; (ii) unit compatibility: the identity element of the convolution monoid `WithConv (H' →ₐ[R] K)` of $R$-algebra maps $H' \to K$, namely $\eta_K \circ \varepsilon_{H'}$, precomposed with $\varphi$ equals the identity element $\eta_K \circ \varepsilon_H$ of `WithConv (H →ₐ[R] K)`; (iii) multiplicativity: for all $\chi, \chi' : H' \to K$ in the convolution monoid, $(\chi * \chi') \circ \varphi = (\chi \circ \varphi) * (\chi' \circ \varphi)$, the convolution on the right being formed in `WithConv (H →ₐ[R] K)`. The conclusion is that there exists a bialgebra homomorphism $\psi : H \to H'$ over $R$ whose underlying $R$-algebra homomorphism is exactly $\varphi$.
--
--   This is the bialgebra form of the statement that a morphism of affine schemes $\operatorname{Spec} H' \to \operatorname{Spec} H$ which is a monoid homomorphism on $K$-valued points, for a single ring $K$ whose $K$-points separate $H' \otimes_R H'$, is a morphism of affine monoid schemes. It is used to upgrade algebra maps to bialgebra maps in the uniqueness statement [`HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero`](thm.html#HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_charZero) and in the recognition of maps between Néron models of modular curves at $p$ ([`ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq`](thm.html#ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq) and its level-data variant).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BialgHom_exists_coe_eq_of_forall_withConv_comp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem BialgHom.exists_coe_eq_of_forall_withConv_comp
    {R : Type u} [CommRing R] {K : Type u} [CommRing K] [Algebra R K] (hinj : Function.Injective (algebraMap R K))
    {H : Type u} [CommRing H] [Bialgebra R H] {H' : Type u} [CommRing H'] [Bialgebra R H']
    (φ : H →ₐ[R] H')
    (hsep : ∀ x : H' ⊗[R] H', (∀ θ : H' ⊗[R] H' →ₐ[R] K, θ x = 0) → x = 0)
    (hone : (1 : WithConv (H' →ₐ[R] K)).ofConv.comp φ = (1 : WithConv (H →ₐ[R] K)).ofConv)
    (hmul : ∀ χ χ' : WithConv (H' →ₐ[R] K),
      (χ * χ').ofConv.comp φ = (WithConv.toConv (χ.ofConv.comp φ) * WithConv.toConv (χ'.ofConv.comp φ)).ofConv) :
    ∃ ψ : H →ₐc[R] H', (ψ : H →ₐ[R] H') = φ := by sorry
