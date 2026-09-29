-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
-- name    : AlgebraicGeometry.SmallExtension.pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e8d411af-5c75-56ee-a307-8c7cd1f6e3a9
-- title:
--   Natural endomorphism determined by its value at M=k
-- statement:
--   Let $k$ be a field and $A$ a commutative $k$-algebra (both in a fixed universe), and let $\mathrm{ev} : A \to k$ be a ring homomorphism. For a $k$-module $M$, write $\mathrm{Der}_{\mathrm{ev}}(A;M)$ for the $k$-submodule [`Algebra.PointDerivations k A ev M`](def/Algebra_PointDerivations.html#L9) of $\mathrm{Hom}_k(A,M)$ consisting of those $D$ with $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$ for all $a,b \in A$, and for $g : M \to M'$ $k$-linear let $g_* =$ [`Algebra.PointDerivations.map ev g`](def/Algebra_PointDerivations.html#L47) be the $k$-linear map $D \mapsto g \circ D$. Let $W$ be a $k$-module, and let $\Phi$ assign to every $k$-module $M$ a $k$-linear isomorphism $\Phi_M : \mathrm{Der}_{\mathrm{ev}}(A;M) \xrightarrow{\sim} W \otimes_k M$, subject to the naturality hypothesis $\Phi_{M'}(g_*\delta) = (\mathrm{id}_W \otimes g)(\Phi_M \delta)$ for all $k$-linear $g : M \to M'$ and all $\delta$. Let $\theta : W \to W$ be $k$-linear, and let $\eta$ assign to every $k$-module $M$ a $k$-linear endomorphism $\eta_M$ of $\mathrm{Der}_{\mathrm{ev}}(A;M)$, subject to the naturality hypothesis $\eta_{M'}(g_*\delta) = g_*(\eta_M \delta)$ and to the pinning condition $\Phi_k(\eta_k \delta) = (\theta \otimes \mathrm{id}_k)(\Phi_k \delta)$ for all $\delta \in \mathrm{Der}_{\mathrm{ev}}(A;k)$. Then for every $k$-module $M$ and every $\delta \in \mathrm{Der}_{\mathrm{ev}}(A;M)$ one has $\eta_M \delta = \Phi_M^{-1}\bigl((\theta \otimes \mathrm{id}_M)(\Phi_M \delta)\bigr)$.
--
--   This is a Yoneda-style rigidity statement: a $k$-linear endomorphism of the functor $M \mapsto \mathrm{Der}_{\mathrm{ev}}(A;M)$, transported through a natural identification with $W \otimes_k M$, is determined by its effect at $M = k$, where it is given by $\theta \otimes \mathrm{id}$. It is used in the treatment of tangent coordinates attached to a point of a scheme, being cited by [`AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot`](thm.html#AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_forall_apply_eq_pushPt_of_mul_maximalIdeal_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq.lean

import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem AlgebraicGeometry.SmallExtension.pointDerivations_natural_endo_eq_symm_map_tmul_of_apply_eq
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)

    (W : Type u) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))

    (θ : W →ₗ[k] W)
    (η : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) →ₗ[k] ↥(Algebra.PointDerivations k A ev M))
    (hηnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      η M' (Algebra.PointDerivations.map ev g δ) = Algebra.PointDerivations.map ev g (η M δ))
    (hηpin : ∀ δ : ↥(Algebra.PointDerivations k A ev k),
      Φ k (η k δ) = TensorProduct.map θ (LinearMap.id : k →ₗ[k] k) (Φ k δ))
    (M : Type u) [AddCommGroup M] [Module k M] (δ : ↥(Algebra.PointDerivations k A ev M)) :
    η M δ = (Φ M).symm (TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) (Φ M δ)) := by sorry
