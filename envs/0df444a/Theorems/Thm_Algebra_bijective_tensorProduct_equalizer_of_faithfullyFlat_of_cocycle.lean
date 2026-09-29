-- Prove2me | Theorems.Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
-- name    : Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/19931af4-157e-5be8-a788-06ac308b8a13
-- title:
--   Faithfully flat descent for graded algebras
-- statement:
--   Let $S$ be a commutative ring, $S'$ a commutative $S$-algebra that is faithfully flat as an $S$-module, and $A'$ a commutative ring carrying compatible $S$- and $S'$-algebra structures (a scalar tower $S \to S' \to A'$), together with an $\mathbb N$-grading $\mathcal A' : \mathbb N \to$ (submodules of $A'$ over $S'$) making $A'$ a graded $S'$-algebra. Let $\varphi : A' \otimes_S S' \simeq S' \otimes_S A'$ be an isomorphism of $S$-algebras subject to three hypotheses: composing the map $S' \otimes_S S' \to A' \otimes_S S'$ induced by the structure map $S' \to A'$ on the left factor with $\varphi$ gives the map $S' \otimes_S S' \to S' \otimes_S A'$ induced by $S' \to A'$ on the right factor; for every $n$, every $a \in \mathcal A'_n$ and every $t \in S'$, $\varphi(a \otimes t)$ lies in the $S'$-base change of $\mathcal A'_n$ viewed as an $S$-submodule, i.e. in the image of $S' \otimes_S \mathcal A'_n$; and the cocycle identity $\varphi_{02} = \varphi_{12}\varphi_{01}$, stated as the equality of two $S$-algebra homomorphisms $(A' \otimes_S S') \otimes_S S' \to S' \otimes_S (S' \otimes_S A')$ built from $\varphi$ in the two outer factors together with the associativity and commutativity isomorphisms of the tensor product. Put $A := \{a \in A' \mid \varphi(a \otimes 1) = 1 \otimes a\}$, the equaliser subalgebra of $\varphi \circ (a \mapsto a \otimes 1)$ and $a \mapsto 1 \otimes a$ as $S$-algebra maps $A' \to S' \otimes_S A'$. The conclusion is twofold: the $S$-algebra homomorphism $S' \otimes_S A \to A'$ determined by the structure map $S' \to A'$ and the inclusion $A \subseteq A'$ is bijective; and for every $a \in A$ and every $n$, the degree-$n$ component of $a$ for the grading $\mathcal A'$ again lies in $A$.
--
--   This is effective faithfully flat descent for a graded algebra: a descent datum $\varphi$ on $A'$ that is compatible with the two structure maps, degree-preserving and satisfies the cocycle condition descends $A'$ to its algebra of invariants $A$, and the grading descends as well. It is deduced from the module-level statement [`Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum`](thm.html#Module.FaithfullyFlat.isBaseChange_eqLocus_of_descentDatum) and is used by [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_cocycle), where descending the graded algebra of sections of a relatively very ample invertible module and forming $\mathrm{Proj}$ yields descent of a projective scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_cocycle
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (𝒜' : ℕ → Submodule S' A') [GradedAlgebra 𝒜']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')

    (hφlin : φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))

    (hφdeg : ∀ (n : ℕ) (a : A'), a ∈ 𝒜' n → ∀ t : S',
      φ (a ⊗ₜ t) ∈ ((𝒜' n).restrictScalars S).baseChange S')

    (hφcoc : (Algebra.TensorProduct.map (AlgHom.id S S') φ.toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          (Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S'))) =
      (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.comm S A' S').toAlgHom).comp
        ((Algebra.TensorProduct.assoc S S S S' A' S').toAlgHom.comp
          ((Algebra.TensorProduct.map φ.toAlgHom (AlgHom.id S S')).comp
            ((Algebra.TensorProduct.assoc S S S A' S' S').symm.toAlgHom.comp
              ((Algebra.TensorProduct.map (AlgHom.id S A') (Algebra.TensorProduct.comm S S' S').toAlgHom).comp
                (Algebra.TensorProduct.assoc S S S A' S' S').toAlgHom)))))
    :
    let A : Subalgebra S A' :=
      AlgHom.equalizer (φ.toAlgHom.comp (Algebra.TensorProduct.includeLeft : A' →ₐ[S] A' ⊗[S] S'))
        (Algebra.TensorProduct.includeRight : A' →ₐ[S] S' ⊗[S] A')
    Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _)) ∧
      (∀ a ∈ A, ∀ n : ℕ, (DirectSum.decompose 𝒜' a n : A') ∈ A) := by sorry
