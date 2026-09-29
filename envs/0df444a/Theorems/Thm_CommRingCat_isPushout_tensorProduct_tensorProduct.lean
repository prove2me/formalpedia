-- Prove2me | Theorems.Thm_CommRingCat_isPushout_tensorProduct_tensorProduct
-- name    : CommRingCat.isPushout_tensorProduct_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/377b4a49-a967-548f-a5a3-ef1f973d4d96
-- title:
--   Triple tensor product as a pushout of commutative rings
-- statement:
--   Let $R$ be a commutative ring and let $A$, $B$, $C$ be commutative rings equipped with $R$-algebra structures, all in a fixed universe. Consider the square in the category `CommRingCat` of commutative rings whose two maps out of $B$ are $\mathrm{includeRight} : B \to A \otimes_R B$, $b \mapsto 1 \otimes b$, and $\mathrm{includeLeft} : B \to B \otimes_R C$, $b \mapsto b \otimes 1$, and whose two maps into $A \otimes_R (B \otimes_R C)$ are $\mathrm{id}_A \otimes \mathrm{includeLeft} : A \otimes_R B \to A \otimes_R (B \otimes_R C)$, $a \otimes b \mapsto a \otimes (b \otimes 1)$, and $\mathrm{includeRight} : B \otimes_R C \to A \otimes_R (B \otimes_R C)$, $y \mapsto 1 \otimes y$ (each $R$-algebra map being regarded as a morphism of commutative rings through its underlying ring homomorphism). The assertion is that this square is a pushout square of commutative rings: it commutes, and the resulting cocone on $A \otimes_R B \leftarrow B \rightarrow B \otimes_R C$ exhibits $A \otimes_R (B \otimes_R C)$ as a colimit, i.e. as $(A \otimes_R B) \otimes_B (B \otimes_R C)$.
--
--   This is the standard associativity/base-change identification of a triple tensor product as an amalgamated tensor product, in the form of a universal property; dually, on spectra it says that $\operatorname{Spec}(A \otimes_R (B \otimes_R C))$ is the fibre product of $\operatorname{Spec}(A \otimes_R B)$ and $\operatorname{Spec}(B \otimes_R C)$ over $\operatorname{Spec} B$. It is used in the construction of invertible modules on schemes from descent data satisfying a cocycle condition, where the third stage of a Čech nerve must be recognised as a fibre product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CommRingCat_isPushout_tensorProduct_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

theorem CommRingCat.isPushout_tensorProduct_tensorProduct
    (R : Type u) [CommRing R] (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] :
    IsPushout
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R A)
        (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] C)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B ⊗[R] C →ₐ[R] A ⊗[R] (B ⊗[R] C)).toRingHom) := by sorry
