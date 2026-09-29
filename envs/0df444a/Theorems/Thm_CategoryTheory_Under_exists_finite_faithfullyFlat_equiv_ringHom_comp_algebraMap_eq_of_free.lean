-- Prove2me | Theorems.Thm_CategoryTheory_Under_exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free
-- name    : CategoryTheory.Under.exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/b2bc67c2-d3fe-5f52-8e28-2712339c4875
-- title:
--   Base change W⊗_{R_0}H corepresents R₀-algebra maps from H
-- statement:
--   Let $R_0$ be a commutative ring and let $H$ be a commutative $R_0$-algebra which is finite and free as an $R_0$-module and nontrivial as a ring, and let $W$ be an arbitrary commutative $R_0$-algebra. The assertion is that there exists a commutative ring $C_1$, carrying $R_0$- and $W$-algebra structures compatible in the sense that $R_0\to W\to C_1$ agrees with $R_0\to C_1$, such that $C_1$ is finite and faithfully flat as a $W$-module, and such that there exists a family of bijections $e$ with the following shape: for every object $B'$ of the category $\mathrm{Under}\,(R_0)$ of commutative rings under $R_0$ and every morphism $b$ from the object $R_0\to W$ to $B'$ in that category, $e_{B',b}$ is a bijection between the set of ring homomorphisms $\chi : H \to B'.\mathrm{right}$ with $\chi\circ(\text{structure map }R_0\to H)$ equal to the structure map of $B'$, and the set of morphisms $g$ from the object $R_0\to C_1$ to $B'$ under $R_0$ such that the morphism under $R_0$ induced by $\mathrm{algebraMap}\;W\;C_1$, followed by $g$, equals $b$. Moreover $e$ is natural in the target: for objects $B',B''$ under $R_0$, a morphism $b$ as above, a morphism $\psi : B'\to B''$ under $R_0$, and such a $\chi$, the underlying morphism of $e_{B'',\,b\circ\psi}(\psi\circ\chi)$ equals the underlying morphism of $e_{B',b}(\chi)$ followed by $\psi$.
--
--   This records that for $H$ finite free and nonzero over $R_0$ the base change $W\otimes_{R_0}H$ is a finite faithfully flat $W$-algebra corepresenting, naturally in the target ring under $R_0$, the $R_0$-algebra homomorphisms out of $H$ with prescribed restriction to $W$. It is used in the construction of a finite faithfully flat cover corepresenting the symmetric-root class functor over $W$, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_finite_faithfullyFlat_corepresents_symmRoot_classFunctor_under).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_Under_exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory TensorProduct

theorem CategoryTheory.Under.exists_finite_faithfullyFlat_equiv_ringHom_comp_algebraMap_eq_of_free
    (R₀ : Type) [CommRing R₀] (H : Type) [CommRing H] [Algebra R₀ H] [Module.Finite R₀ H] [Module.Free R₀ H] [Nontrivial H]
    (W : Type) [CommRing W] [Algebra R₀ W] :
    ∃ (C₁ : Type) (_ : CommRing C₁) (_ : Algebra R₀ C₁) (_ : Algebra W C₁) (_ : IsScalarTower R₀ W C₁),
      Module.Finite W C₁ ∧ Module.FaithfullyFlat W C₁ ∧
      ∃ e : ∀ (B' : Under (CommRingCat.of R₀)) (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B'),
          {χ : H →+* B'.right // χ.comp (algebraMap R₀ H) = B'.hom.hom} ≃
            {g : Under.mk (CommRingCat.ofHom (algebraMap R₀ C₁)) ⟶ B' //
              Under.homMk (U := Under.mk (CommRingCat.ofHom (algebraMap R₀ W)))
                  (V := Under.mk (CommRingCat.ofHom (algebraMap R₀ C₁)))
                  (CommRingCat.ofHom (algebraMap W C₁)) (by ext r; exact (IsScalarTower.algebraMap_apply R₀ W C₁ r).symm) ≫ g = b},
        ∀ (B' B'' : Under (CommRingCat.of R₀)) (b : Under.mk (CommRingCat.ofHom (algebraMap R₀ W)) ⟶ B')
          (ψ : B' ⟶ B'') (χ : {χ : H →+* B'.right // χ.comp (algebraMap R₀ H) = B'.hom.hom}),
          ((e B'' (b ≫ ψ)) ⟨ψ.right.hom.comp χ.1, by rw [RingHom.comp_assoc, χ.2, ← CommRingCat.hom_comp, Under.w ψ]⟩).1 =
            ((e B' b) χ).1 ≫ ψ := by sorry
