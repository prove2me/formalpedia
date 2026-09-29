-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_cocycle_of_rigidified
-- name    : AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_cocycle_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/59aff909-5587-5e85-9915-61bb5e131225
-- title:
--   Rigidified descent data for line bundles satisfy the cocycle condition
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra. Let $f' : X' \to \operatorname{Spec} S'$ be a morphism of schemes with a section $e'$, so $e' \gg f' = \mathbf 1$, and let $L'$ be a module on $X'$ which is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $X'$ has an open neighbourhood $U$ such that the pullback of $L'$ along $U \hookrightarrow X'$ is isomorphic to the unit sheaf of modules of $U$; assume moreover $L'$ is rigidified, i.e. $(e')^*L'$ is isomorphic to the unit sheaf of modules of $\operatorname{Spec} S'$. Let $f'' : X'' \to \operatorname{Spec}(S' \otimes_S S')$ and $f''' : X''' \to \operatorname{Spec}(S' \otimes_S (S' \otimes_S S'))$ be morphisms whose maps on global sections are surjective, let $a_1, a_2 : X'' \to X'$ make the squares over $\operatorname{Spec}$ of the left and right inclusions $S' \to S' \otimes_S S'$ cartesian, and let $b_{12}, b_{13}, b_{23} : X''' \to X''$ make the squares over $\operatorname{Spec}$ of $\mathrm{id} \otimes \mathrm{includeLeft}$, $\mathrm{id} \otimes \mathrm{includeRight}$ and the right inclusion $S' \otimes_S S' \to S' \otimes_S (S' \otimes_S S')$ cartesian. Assume the nerve identities $b_{12} \gg a_1 = b_{13} \gg a_1$, $b_{12} \gg a_2 = b_{23} \gg a_1$, $b_{13} \gg a_2 = b_{23} \gg a_2$, and that $f''$ has a section $e''$ with $e'' \gg a_i$ equal to $\operatorname{Spec}$ of the $i$-th inclusion followed by $e'$ for $i = 1, 2$. Assume finally that $a_1^*L'$ and $a_2^*L'$ are isomorphic. Then there exists an isomorphism $\psi : a_1^*L' \xrightarrow{\sim} a_2^*L'$ satisfying the cocycle condition on $X'''$: the composite of $b_{12}^*\psi$ and $b_{23}^*\psi$, transported through the canonical comparison isomorphisms for composite pullbacks and the identifications coming from the three nerve identities, equals $b_{13}^*\psi$ transported likewise.
--
--   This is the line-bundle half of effective faithfully flat descent: any isomorphism between the two pullbacks of a rigidified invertible module can be normalised along the sections so as to become a genuine descent datum on the Čech nerve. It is used by [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_rigidified`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_rigidified), and the normalisation is obtained from the existence and uniqueness statements `Scheme.Modules.exists_iso_pullback_map_eq_of_nonempty_iso`, `Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop` and `Scheme.Modules.pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_pullback_cocycle_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_cocycle_of_rigidified
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (e' : Spec (CommRingCat.of S') ⟶ X') (he' : e' ≫ f' = 𝟙 _)
    (L' : X'.Modules) (hL' : Scheme.Modules.IsInvertible L')
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
    ∃ ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L',

      ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫ ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫ (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L') := by sorry
