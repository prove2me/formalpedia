-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_rigidified
-- name    : AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/1a3cd861-8cdb-5d21-b9a6-f32fc5c78f5e
-- title:
--   Effective faithfully flat descent for rigidified very ample line bundles
-- statement:
--   Let $S \to S'$ be a faithfully flat ring map of commutative rings in a fixed universe. The data are: a scheme $X'$ with $f' : X' \to \operatorname{Spec} S'$, a section $e'$ of $f'$ (i.e. $e' \gg f' = \mathrm{id}$), surjectivity of $\Gamma$ of $f'$ on global sections, a module $L'$ on $X'$ which is invertible in the sense that every point of $X'$ has an open neighbourhood $U$ on which the pullback of $L'$ along $U \hookrightarrow X'$ is isomorphic to the structure sheaf of $U$, and such that `ClosedImmersionBySections L' f'` holds: for some $N$ there are global sections $\sigma_0,\dots,\sigma_N$ of $L'$ together with a morphism $X' \to \mathbf{P}^N_{S'} = \operatorname{Proj}$ of the graded polynomial ring in $N+1$ variables over $S'$ whose composite with the projection is $f'$, such that over the preimage of the $i$-th standard chart multiplication by $\sigma_i$ is a bijection $\Gamma(X',V) \to \Gamma(L',V)$ and the ratio $X_j/X_i$ carries $\sigma_i$ to $\sigma_j$, and this morphism to projective space is a closed immersion; a rigidification, namely an isomorphism $e'^*L' \cong \mathcal{O}_{\operatorname{Spec} S'}$; a scheme $X''$ over $\operatorname{Spec}(S' \otimes_S S')$ with surjective global sections map and two morphisms $a_1,a_2 : X'' \to X'$ making cartesian squares over $\operatorname{Spec}$ of the left and right inclusions $S' \to S' \otimes_S S'$; a scheme $X'''$ over $\operatorname{Spec}(S' \otimes_S (S' \otimes_S S'))$ with surjective global sections map and three morphisms $b_{12},b_{13},b_{23} : X''' \to X''$ cartesian over $\operatorname{Spec}$ of the three corresponding inclusions $S' \otimes_S S' \to S' \otimes_S (S' \otimes_S S')$, subject to the simplicial identities $b_{12} \gg a_1 = b_{13} \gg a_1$, $b_{12} \gg a_2 = b_{23} \gg a_1$, $b_{13} \gg a_2 = b_{23} \gg a_2$; a section $e''$ of $X'' \to \operatorname{Spec}(S' \otimes_S S')$ compatible with $e'$ via $a_1$ and $a_2$; and an isomorphism $a_1^*L' \cong a_2^*L'$ (no cocycle condition on it is assumed). The conclusion is the existence of a scheme $X$, a morphism $f : X \to \operatorname{Spec} S$ and a morphism $c : X' \to X$ such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of $S \to S'$ is cartesian, $a_1 \gg c = a_2 \gg c$, and there is a module $L$ on $X$, invertible in the above sense, with $c^*L \cong L'$.
--
--   This is effectivity of faithfully flat descent for a scheme together with a relatively very ample invertible module, in the form in which the gluing datum on the line bundle is only required to be a rigidified isomorphism over $S' \otimes_S S'$ rather than a full cocycle. It is the form used to descend line bundles on abelian schemes, where global functions come from the base, and is consumed in turn by the variant [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_closedImmersionBySections_of_rigidified`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_closedImmersionBySections_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_descent_of_faithfullyFlat_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_rigidified
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']

    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (e' : Spec (CommRingCat.of S') ⟶ X') (he' : e' ≫ f' = 𝟙 _)
    (hΓ' : Function.Surjective (f'.appTop).hom)
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L') (hva : Scheme.Modules.ClosedImmersionBySections L' f')

    (hrig : Nonempty ((Scheme.Modules.pullback e').obj L' ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf))

    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S')))
    (hΓ'' : Function.Surjective (f''.appTop).hom)
    (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))

    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (hΓ''' : Function.Surjective (f'''.appTop).hom)
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)

    (e'' : Spec (CommRingCat.of (S' ⊗[S] S')) ⟶ X'') (he'' : e'' ≫ f'' = 𝟙 _)
    (hea₁ : e'' ≫ a₁ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ e')
    (hea₂ : e'' ≫ a₂ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ e')

    (hL'' : Nonempty ((Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X)
      (_ : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))),
      a₁ ≫ c = a₂ ≫ c ∧
      ∃ (L : X.Modules), Scheme.Modules.IsInvertible L ∧
        Nonempty ((Scheme.Modules.pullback c).obj L ≅ L') := by sorry
