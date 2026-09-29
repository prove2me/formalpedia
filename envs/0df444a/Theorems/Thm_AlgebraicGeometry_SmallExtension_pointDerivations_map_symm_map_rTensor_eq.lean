-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq
-- name    : AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/819f237d-d9b2-5e5e-afe8-4420620cfac7
-- title:
--   Naturality of the θ-twist on point derivations
-- statement:
--   Let $k$ be a field and $A$ a commutative $k$-algebra, let $\mathrm{ev} : A \to k$ be a ring homomorphism, and let $W$ be a $k$-module. For a $k$-module $M$ write $\mathrm{PDer}(M)$ for the $k$-submodule of $\mathrm{Hom}_k(A, M)$ consisting of those $D$ with $D(ab) = \mathrm{ev}(a)\cdot D(b) + \mathrm{ev}(b)\cdot D(a)$ for all $a, b \in A$, and for a $k$-linear $\varphi : M \to M'$ let $\varphi_*$ denote the induced $k$-linear map $\mathrm{PDer}(M) \to \mathrm{PDer}(M')$, $D \mapsto \varphi \circ D$. Assume given a family of $k$-linear isomorphisms $\Phi_M : \mathrm{PDer}(M) \xrightarrow{\sim} W \otimes_k M$, one for each $k$-module $M$, which is natural in $M$ in the sense that $\Phi_{M'}(g_*\delta) = (\mathrm{id}_W \otimes g)(\Phi_M \delta)$ for every $k$-linear $g : M \to M'$ and every $\delta \in \mathrm{PDer}(M)$. Let $\theta : W \to W$ be $k$-linear. Then for all $k$-modules $M$, $M'$, every $k$-linear $g : M \to M'$ and every $\delta \in \mathrm{PDer}(M)$,
--   $$g_*\bigl(\Phi_M^{-1}((\theta \otimes \mathrm{id}_M)\,\Phi_M \delta)\bigr) = \Phi_{M'}^{-1}\bigl((\theta \otimes \mathrm{id}_{M'})\,\Phi_{M'}(g_*\delta)\bigr),$$
--   an identity in $\mathrm{PDer}(M')$.
--
--   The statement says that the endomorphism of point-derivation modules obtained by transporting $\theta \otimes \mathrm{id}$ through a natural identification $\mathrm{PDer}(M) \cong W \otimes_k M$ is itself natural in the coefficient module $M$. It is used in the deformation-theoretic part of the argument, where such twists of tangent/derivation modules are compared along maps of coefficient modules: it is invoked in the analysis of local lifts and of the obstruction cocycle for bare deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_pointDerivations_map_symm_map_rTensor_eq.lean

import Mathlib
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

universe u

theorem AlgebraicGeometry.SmallExtension.pointDerivations_map_symm_map_rTensor_eq
    {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A] (ev : A →+* k)
    (W : Type u) [AddCommGroup W] [Module k W]
    (Φ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (W ⊗[k] M))
    (hΦnat : ∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
        (δ : ↥(Algebra.PointDerivations k A ev M)),
      Φ M' (Algebra.PointDerivations.map ev g δ) = TensorProduct.map (LinearMap.id : W →ₗ[k] W) g (Φ M δ))
    (θ : W →ₗ[k] W)
    (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
    (δ : ↥(Algebra.PointDerivations k A ev M)) :
    Algebra.PointDerivations.map ev g ((Φ M).symm (TensorProduct.map θ (LinearMap.id : M →ₗ[k] M) (Φ M δ))) =
      (Φ M').symm (TensorProduct.map θ (LinearMap.id : M' →ₗ[k] M') (Φ M' (Algebra.PointDerivations.map ev g δ))) := by sorry
