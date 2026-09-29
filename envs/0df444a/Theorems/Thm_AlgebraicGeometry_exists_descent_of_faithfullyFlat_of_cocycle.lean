-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_cocycle
-- name    : AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/5f2bed59-787c-532e-a499-10bf8026662d
-- title:
--   Effective faithfully flat descent for relatively very ample invertible modules
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra that is faithfully flat as an $S$-module. Let $f' : X' \to \operatorname{Spec} S'$ be a scheme over $S'$ and let $L'$ be an $\mathcal{O}_{X'}$-module that is invertible in the sense that every point of $X'$ has an open neighbourhood $U$ on which the pullback of $L'$ along $U \hookrightarrow X'$ is isomorphic to the unit sheaf of modules, and which satisfies `Scheme.Modules.ClosedImmersionBySections L' f'`: for some $N$ there are global sections $\sigma_0,\dots,\sigma_N$ of $L'$ and a morphism $\theta : X' \to \mathbb{P}^N_{S'} = \operatorname{Proj}$ of the homogeneous subalgebra of $S'[X_0,\dots,X_N]$, compatible with the structure morphisms, such that over $\theta^{-1}(D(X_i))$ multiplication by $\sigma_i$ is bijective from functions to sections of $L'$ and the pulled-back ratio $X_j/X_i$ carries $\sigma_i$ to $\sigma_j$, and such that $\theta$ is a closed immersion. Let $f'' : X'' \to \operatorname{Spec}(S' \otimes_S S')$ be given together with $a_1, a_2 : X'' \to X'$ making $X''$ cartesian over $X'$ along $\operatorname{Spec}$ of the left and right inclusions, and $f''' : X''' \to \operatorname{Spec}(S' \otimes_S (S' \otimes_S S'))$ with $b_{12}, b_{13}, b_{23} : X''' \to X''$ cartesian along $\operatorname{Spec}$ of $\mathrm{id} \otimes \text{includeLeft}$, $\mathrm{id} \otimes \text{includeRight}$ and the right inclusion $S' \otimes_S S' \to S' \otimes_S (S' \otimes_S S')$ respectively, subject to the nerve identities $b_{12} \circ a_1 = b_{13} \circ a_1$, $b_{12} \circ a_2 = b_{23} \circ a_1$, $b_{13} \circ a_2 = b_{23} \circ a_2$ (written diagrammatically). Let $\psi : a_1^* L' \cong a_2^* L'$ be an isomorphism of modules satisfying the cocycle condition on $X'''$, expressed as the stated equality of composites of the pullbacks of $\psi$ along $b_{12}$, $b_{23}$ and $b_{13}$ with the canonical comparison isomorphisms for composition of pullbacks and for the three nerve identities. Then the datum is effective: there exist a scheme $X$, a morphism $f : X \to \operatorname{Spec} S$ and $c : X' \to X$ exhibiting $X'$ as the pullback of $X$ along $\operatorname{Spec}$ of $S \to S'$, with $a_1 \circ c = a_2 \circ c$, and an invertible $\mathcal{O}_X$-module $L$ admitting an isomorphism $c^* L \cong L'$. The conclusion records only the existence of such an isomorphism, not its compatibility with $\psi$, and asserts nothing about relative very ampleness of $L$.
--
--   This is the effectivity part of faithfully flat descent for schemes carrying a relatively very ample invertible module, in the Čech-nerve formulation with an explicit cocycle isomorphism (SGA 1, Exposé VIII, 7.8; Bosch–Lütkebohmert–Raynaud, §6.1). It is used by the rigidified variant [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_rigidified`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_rigidified), where the cocycle is normalised along a section, in the construction of relative Picard functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_cocycle.lean

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S'))
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L') (hva : Scheme.Modules.ClosedImmersionBySections L' f')
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
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X)
      (_ : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))),
      a₁ ≫ c = a₂ ≫ c ∧
      ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
        Nonempty ((Scheme.Modules.pullback c).obj L ≅ L') := by sorry
