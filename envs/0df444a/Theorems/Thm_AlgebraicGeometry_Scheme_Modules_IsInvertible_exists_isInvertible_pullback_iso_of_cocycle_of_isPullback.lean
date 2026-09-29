-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/b635ffc3-eeea-5fa1-9afb-29e46d93ab9d
-- title:
--   Descent of invertible modules along a faithfully flat base change
-- statement:
--   Fix a commutative ring $S$ and a commutative $S$-algebra $S'$ that is faithfully flat as an $S$-module. Let $X'$ be a scheme with a morphism $f' : X' \to \operatorname{Spec} S'$ and let $L'$ be an $X'$-module that is invertible in the sense that every point of $X'$ has an open neighbourhood $U$ on which the restriction of $L'$ along $U \hookrightarrow X'$ is isomorphic to the unit module of the structure sheaf of $U$. Let $X''$ carry $f'' : X'' \to \operatorname{Spec}(S' \otimes_S S')$ together with $a_1, a_2 : X'' \to X'$ making the two squares over $\operatorname{Spec}$ of the left and right inclusions $S' \to S' \otimes_S S'$ cartesian, and let $X'''$ carry $f''' : X''' \to \operatorname{Spec}(S' \otimes_S (S' \otimes_S S'))$ together with $b_{12}, b_{13}, b_{23} : X''' \to X''$ making the squares over $\operatorname{Spec}$ of $\mathrm{id} \otimes \text{includeLeft}$, $\mathrm{id} \otimes \text{includeRight}$ and the right inclusion $S' \otimes_S S' \to S' \otimes_S (S' \otimes_S S')$ cartesian; assume the nerve identities $b_{12} \circ a_1 = b_{13} \circ a_1$, $b_{12} \circ a_2 = b_{23} \circ a_1$, $b_{13} \circ a_2 = b_{23} \circ a_2$ (written diagrammatically). Let $\psi : a_1^* L' \cong a_2^* L'$ be an isomorphism of $X''$-modules satisfying the cocycle condition on $X'''$, stated as the equality of the composite of the $b_{12}$- and $b_{23}$-pullbacks of $\psi$ with the $b_{13}$-pullback of $\psi$, after insertion of the canonical comparison isomorphisms for composition of pullbacks and for equal morphisms. Finally let $X$ carry $f : X \to \operatorname{Spec} S$ and $c : X' \to X$ with the square over $\operatorname{Spec}$ of $S \to S'$ cartesian and with $a_1 \circ c = a_2 \circ c$. Then there exists an $X$-module $L$, invertible in the same local sense, such that $c^* L \cong L'$.
--
--   This is effectivity of descent data for invertible modules along a faithfully flat base change of the base ring, the scheme-level descent being supplied as a hypothesis in the form of the cartesian squares over the Čech nerve of $S \to S'$. It is used in the construction of descended line bundles and polarisations, being cited by the descent statement for faithfully flat covers with a cocycle and by the corresponding statement for polarisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_pullback_iso_of_cocycle_of_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_pullback_iso_of_cocycle_of_isPullback
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L')
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L'))
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))) (hca : a₁ ≫ c = a₂ ≫ c) :
    ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧ Nonempty ((Scheme.Modules.pullback c).obj L ≅ L') := by sorry
