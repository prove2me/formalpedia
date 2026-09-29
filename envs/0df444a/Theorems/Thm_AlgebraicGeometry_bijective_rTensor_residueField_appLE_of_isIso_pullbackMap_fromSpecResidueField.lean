-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
-- name    : AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2b1f5da4-234a-5c31-bf02-30ece72451ca
-- title:
--   Fibre isomorphism gives bijection on sections after base change to κ(y)
-- statement:
--   Let $X$, $Y$, $Z$ be schemes (in the bottom universe) and let $p : Z \to Y$, $q : X \to Y$, $h : Z \to X$ be morphisms with $h$ followed by $q$ equal to $p$. Fix a point $y$ of $Y$ and assume that the canonical morphism of pullbacks $Z \times_Y \operatorname{Spec}\kappa(y) \to X \times_Y \operatorname{Spec}\kappa(y)$ induced by $h$ over $Y$ together with the identity of $\operatorname{Spec}\kappa(y)$ — formed from the two copies of `Y.fromSpecResidueField y` — is an isomorphism. Let $W$ be an open of $Y$ which is affine and contains $y$, and let $U$ be an affine open of $X$ contained in $q^{-1}(W)$ whose preimage $h^{-1}(U)$ is again affine. Give $\Gamma(X,U)$ the $\Gamma(Y,W)$-algebra structure coming from the restriction $q^{\sharp} : \Gamma(Y,W) \to \Gamma(X,U)$, give $\Gamma(Z,h^{-1}(U))$ the structure coming from that map followed by $h^{\sharp} : \Gamma(X,U) \to \Gamma(Z,h^{-1}(U))$, and give the residue field $\kappa(y)$ the structure coming from evaluation at $y$ on $\Gamma(Y,W)$. Then $h^{\sharp}$, viewed as a $\Gamma(Y,W)$-algebra map and tensored on the right with $\kappa(y)$, is bijective: $$\Gamma(X,U)\otimes_{\Gamma(Y,W)}\kappa(y) \;\longrightarrow\; \Gamma(Z,h^{-1}(U))\otimes_{\Gamma(Y,W)}\kappa(y)$$ is a bijection.
--
--   This is the affine-chart form of the statement that an isomorphism between the fibres over $y$ of two $Y$-schemes is detected on rings of sections after base change to the residue field $\kappa(y)$: on affine opens $W \subseteq Y$, $U \subseteq q^{-1}(W)$ with $h^{-1}(U)$ affine, the fibres of $U$ and $h^{-1}(U)$ over $y$ are the spectra of $\Gamma(X,U)\otimes_{\Gamma(Y,W)}\kappa(y)$ and $\Gamma(Z,h^{-1}(U))\otimes_{\Gamma(Y,W)}\kappa(y)$. It feeds the local analysis of morphisms which are isomorphisms on a fibre, being used in [`AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField`](thm.html#AlgebraicGeometry.exists_mem_and_isIso_morphismRestrict_of_isClosedImmersion_pullbackMap_opens_of_isIso_pullbackMap_fromSpecResidueField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TensorProduct

theorem AlgebraicGeometry.bijective_rTensor_residueField_appLE_of_isIso_pullbackMap_fromSpecResidueField
    {X Y Z : Scheme.{0}} (p : Z ⟶ Y) (q : X ⟶ Y) (h : Z ⟶ X) (w : h ≫ q = p)
    (y : Y) (hy : IsIso (pullback.map p (Y.fromSpecResidueField y) q (Y.fromSpecResidueField y) h (𝟙 _) (𝟙 _)
          (by rw [Category.comp_id, w]) (by rw [Category.comp_id, Category.id_comp])))
    (W : Y.Opens) (hW : IsAffineOpen W) (hyW : y ∈ W)
    (U : X.Opens) (hU : IsAffineOpen U) (hUW : U ≤ q ⁻¹ᵁ W) (hhU : IsAffineOpen (h ⁻¹ᵁ U)) :
    letI : Algebra Γ(Y, W) Γ(X, U) := (q.appLE W U hUW).hom.toAlgebra
    letI : Algebra Γ(Y, W) Γ(Z, h ⁻¹ᵁ U) := (q.appLE W U hUW ≫ h.appLE U (h ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI : Algebra Γ(Y, W) (Y.residueField y) := (Y.evaluation W y hyW).hom.toAlgebra
    Function.Bijective
      ((AlgHom.mk (h.appLE U (h ⁻¹ᵁ U) le_rfl).hom (fun _ => rfl) :
          Γ(X, U) →ₐ[Γ(Y, W)] Γ(Z, h ⁻¹ᵁ U)).toLinearMap.rTensor (Y.residueField y)) := by sorry
