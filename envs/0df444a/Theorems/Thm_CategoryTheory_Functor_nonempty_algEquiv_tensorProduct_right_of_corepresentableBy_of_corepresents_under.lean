-- Prove2me | Theorems.Thm_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
-- name    : CategoryTheory.Functor.nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/05bed1cd-5086-508b-bd4d-0679c2ca973f
-- title:
--   Corepresenting algebra base-changes to the S₁-corepresenting algebra
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a set-valued functor on the category $\mathrm{Under}\,(R)$ of commutative rings equipped with a ring map from $R$. Suppose $F$ is corepresented by an object $C$ of that category, in the sense of `CorepresentableBy`: $F$ is naturally isomorphic to $\mathrm{Hom}(C,-)$. Let $S_1$ be an $R$-algebra and let $C_1$ be a ring carrying compatible $R$- and $S_1$-algebra structures, the compatibility being a scalar-tower condition for $R$, $S_1$, $C_1$. Assume given, for every object $B'$ of $\mathrm{Under}\,(R)$ and every morphism $b$ from $R \to S_1$ to $B'$ (equivalently, every $R$-algebra map $S_1 \to B'$), a bijection between $F(B')$ and the set of morphisms $g$ from $R \to C_1$ to $B'$ whose precomposition with the structural morphism $S_1 \to C_1$ equals $b$ — that is, $F(B') \simeq \mathrm{Hom}_{S_1}(C_1, B')$ — and assume these bijections are natural: for $\psi : B' \to B''$ and $x \in F(B')$, the morphism attached to $F(\psi)(x)$ over $b \circ \psi$ is the morphism attached to $x$ over $b$ followed by $\psi$. Then, with the $R$-algebra structure on the underlying ring $C.\mathrm{right}$ of $C$ given by its structure map, there exists an $S_1$-algebra isomorphism $S_1 \otimes_R C.\mathrm{right} \cong C_1$.
--
--   This is the uniqueness of corepresenting objects (Yoneda) combined with the fact that base change along $R \to S_1$ turns $\mathrm{Hom}_R(C,-)$ into $\mathrm{Hom}_{S_1}(S_1 \otimes_R C,-)$, packaged so that the data $(C_1, e, he)$ appear exactly as they arise in affine faithfully flat descent of corepresentability. It is used in the good-reduction theory of abelian schemes, to identify an algebra obtained by descent with the base change of the corepresenting algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_Functor_nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

theorem CategoryTheory.Functor.nonempty_algEquiv_tensorProduct_right_of_corepresentableBy_of_corepresents_under
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (C : Under (CommRingCat.of R)) (hC : F.CorepresentableBy C)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B'),
      F.obj B' ≃
        {g : Under.mk (CommRingCat.ofHom (algebraMap R C₁)) ⟶ B' //
          Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R S₁)))
              (V := Under.mk (CommRingCat.ofHom (algebraMap R C₁)))
              (CommRingCat.ofHom (algebraMap S₁ C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R S₁ C₁ r).symm) ≫ g = b})
    (he : ∀ (B' B'' : Under (CommRingCat.of R)) (b : Under.mk (CommRingCat.ofHom (algebraMap R S₁)) ⟶ B')
      (ψ : B' ⟶ B'') (x : F.obj B'), ((e B'' (b ≫ ψ)) (F.map ψ x)).1 = ((e B' b) x).1 ≫ ψ) :
    letI : Algebra R C.right := C.hom.hom.toAlgebra
    Nonempty (S₁ ⊗[R] C.right ≃ₐ[S₁] C₁) := by sorry
