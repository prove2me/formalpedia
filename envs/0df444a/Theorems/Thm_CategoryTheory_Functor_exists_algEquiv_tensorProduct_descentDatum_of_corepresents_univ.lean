-- Prove2me | Theorems.Thm_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
-- name    : CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/bb921f35-f606-5429-84a6-ddf0c398e094
-- title:
--   Descent datum on an algebra corepresenting a functor after base change
-- statement:
--   Let $R$ be a commutative ring and let $F$ be a functor from the category of $R$-algebras (objects under `CommRingCat.of R`) to sets in an arbitrary universe $v$, independent of the universe $u$ of $R$. Let $S_1$ be a commutative $R$-algebra and $C_1$ a commutative ring carrying compatible $R$- and $S_1$-algebra structures, with structure map $\iota =$ `IsScalarTower.toAlgHom R S₁ C₁ : S₁ →ₐ[R] C₁`. Assume given, for every commutative $R$-algebra $B$ and every $R$-algebra map $j : S_1 \to B$, a bijection $e_{B,j}$ from $F(B)$ onto the set of $R$-algebra maps $g : C_1 \to B$ with $g \circ \iota = j$, and assume these bijections are natural: for all $R$-algebras $B, B'$, all $j : S_1 \to B$, all $\psi : B \to B'$ and all $x \in F(B)$, the map attached to the image of $x$ under $F(\psi)$ and to $\psi \circ j$ equals $\psi \circ e_{B,j}(x)$. Then there exists an $R$-algebra isomorphism $\varphi : C_1 \otimes_R S_1 \to S_1 \otimes_R C_1$ such that: (i) $\varphi \circ (\iota \otimes \mathrm{id}_{S_1}) = \mathrm{id}_{S_1} \otimes \iota$, so that $\varphi$ is compatible with the two $S_1 \otimes_R S_1$-algebra structures; (ii) $\varphi$ satisfies the cocycle condition on triple tensor products, spelled out as an equality of two $R$-algebra maps built from $\varphi$ together with the canonical associativity and commutativity isomorphisms of tensor products; and (iii) $\varphi$ intertwines the two corepresentations: for every commutative $R$-algebra $D$, every $R$-algebra map $d : S_1 \otimes_R S_1 \to D$ and every $x \in F(D)$, the map $C_1 \otimes_R S_1 \to D$ obtained by tensoring the classifying map $e_{D, d \circ i_1}(x)$ with $d \circ i_2$ equals $\varphi$ followed by the map $S_1 \otimes_R C_1 \to D$ obtained by tensoring $d \circ i_1$ with $e_{D, d \circ i_2}(x)$, where $i_1, i_2 : S_1 \to S_1 \otimes_R S_1$ are the two inclusions.
--
--   This produces the canonical descent datum on an algebra that corepresents a functor of points after base change to $S_1$, with conditions (i) and (ii) in exactly the shape required by the theorem on effectivity of descent for algebras. It is used in the construction of a corepresenting object over the base from one over a faithfully flat extension, for a functor satisfying the relevant sheaf condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_Functor_exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u v

theorem CategoryTheory.Functor.exists_algEquiv_tensorProduct_descentDatum_of_corepresents_univ
    {R : Type u} [CommRing R] (F : Under (CommRingCat.of R) ⥤ Type v)
    (S₁ : Type u) [CommRing S₁] [Algebra R S₁]
    (C₁ : Type u) [CommRing C₁] [Algebra R C₁] [Algebra S₁ C₁] [IsScalarTower R S₁ C₁]
    (e : ∀ (B : Type u) [CommRing B] [Algebra R B] (j : S₁ →ₐ[R] B),
      F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B))) ≃
        {g : C₁ →ₐ[R] B // g.comp (IsScalarTower.toAlgHom R S₁ C₁) = j})
    (he : ∀ (B B' : Type u) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
      (j : S₁ →ₐ[R] B) (ψ : B →ₐ[R] B') (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R B)))),
      ((e B' (ψ.comp j)) (F.map (Under.homMk (CommRingCat.ofHom ψ.toRingHom)
        (by ext r; exact ψ.commutes r)) x)).1 = ψ.comp ((e B j) x).1) :
    ∃ φ : C₁ ⊗[R] S₁ ≃ₐ[R] S₁ ⊗[R] C₁,
      φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S₁ C₁) (AlgHom.id R S₁)) =
        Algebra.TensorProduct.map (AlgHom.id R S₁) (IsScalarTower.toAlgHom R S₁ C₁) ∧
      (Algebra.TensorProduct.map (AlgHom.id R S₁) φ.toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁))) =
        (Algebra.TensorProduct.map (AlgHom.id R S₁) (Algebra.TensorProduct.comm R C₁ S₁).toAlgHom).comp
          ((Algebra.TensorProduct.assoc R R R S₁ C₁ S₁).toAlgHom.comp
            ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id R S₁)).comp
              ((Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).symm.toAlgHom.comp
                ((Algebra.TensorProduct.map (AlgHom.id R C₁) (Algebra.TensorProduct.comm R S₁ S₁).toAlgHom).comp
                  (Algebra.TensorProduct.assoc R R R C₁ S₁ S₁).toAlgHom)))) ∧
      ∀ (D : Type u) [CommRing D] [Algebra R D] (d : S₁ ⊗[R] S₁ →ₐ[R] D)
        (x : F.obj (Under.mk (CommRingCat.ofHom (algebraMap R D)))),
        Algebra.TensorProduct.lift
            ((e D (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            (fun _ _ => Commute.all _ _) =
          (Algebra.TensorProduct.lift
            (d.comp (Algebra.TensorProduct.includeLeft : S₁ →ₐ[R] S₁ ⊗[R] S₁))
            ((e D (d.comp (Algebra.TensorProduct.includeRight : S₁ →ₐ[R] S₁ ⊗[R] S₁))) x).1
            (fun _ _ => Commute.all _ _)).comp φ.toAlgHom := by sorry
