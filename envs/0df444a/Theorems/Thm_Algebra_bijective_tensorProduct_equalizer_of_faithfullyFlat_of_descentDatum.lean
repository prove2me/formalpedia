-- Prove2me | Theorems.Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
-- name    : Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/1238107b-84a8-5bfe-891d-7a1d8d237d92
-- title:
--   Effective faithfully flat descent for commutative algebras
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat as an $S$-module, and let $A'$ be a commutative ring carrying compatible $S$- and $S'$-algebra structures (a scalar tower $S \to S' \to A'$), all in one universe. Let $\varphi \colon A' \otimes_S S' \to S' \otimes_S A'$ be an isomorphism of $S$-algebras subject to two conditions. First, compatibility with the structure maps: the composite of $\iota \otimes \mathrm{id}_{S'} \colon S' \otimes_S S' \to A' \otimes_S S'$, where $\iota \colon S' \to A'$ is the structure map, with $\varphi$ equals $\mathrm{id}_{S'} \otimes \iota$, i.e. $\varphi(\iota(s) \otimes t) = s \otimes \iota(t)$. Second, the cocycle condition on the threefold tensor product, stated as the equality of two $S$-algebra maps $(A' \otimes_S S') \otimes_S S' \to S' \otimes_S (S' \otimes_S A')$: applying $\varphi$ in the first two factors, reassociating and then applying $\varphi$ in the last two factors agrees with transposing the two copies of $S'$, applying $\varphi$ once and transposing again (the usual $\varphi_{02} = \varphi_{12}\varphi_{01}$, written with Mathlib's associativity and commutativity isomorphisms). Let $A \subseteq A'$ be the $S$-subalgebra equalising the two $S$-algebra maps $A' \to S' \otimes_S A'$ given by $a \mapsto \varphi(a \otimes 1)$ and $a \mapsto 1 \otimes a$. Then the canonical $S'$-algebra map $S' \otimes_S A \to A'$, $s \otimes a \mapsto s\,a$, obtained from $\iota$ and the inclusion $A \hookrightarrow A'$, is bijective.
--
--   This is effectivity of faithfully flat descent for commutative algebras in affine form: an algebra equipped with a descent datum along $S \to S'$ is the base change of its algebra of invariants. It is used in the construction of representing objects for functors that are sheaves for the faithfully flat topology, via [`CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ`](thm.html#CategoryTheory.Functor.exists_corepresentableBy_of_faithfullyFlat_of_sheaf_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open TensorProduct Algebra.TensorProduct

theorem Algebra.bijective_tensorProduct_equalizer_of_faithfullyFlat_of_descentDatum
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (A' : Type u) [CommRing A'] [Algebra S A'] [Algebra S' A'] [IsScalarTower S S' A']
    (φ : A' ⊗[S] S' ≃ₐ[S] S' ⊗[S] A')

    (hφlin : φ.toAlgHom.comp (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S S' A') (AlgHom.id S S')) =
      Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom S S' A'))

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
    Function.Bijective (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S S' A') A.val (fun s a => Commute.all _ _)) := by sorry
