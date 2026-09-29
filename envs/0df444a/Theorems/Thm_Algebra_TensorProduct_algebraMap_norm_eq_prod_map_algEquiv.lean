-- Prove2me | Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
-- name    : Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/caef3029-ecdc-5bd8-915e-0fb6746f3c2e
-- title:
--   Base-changed norm as product of Galois conjugates
-- statement:
--   Let $F$ and $M$ be fields with $M$ an $F$-algebra that is finite-dimensional over $F$ and Galois over $F$, and let $R$ be a commutative ring that is an $F$-algebra. For $z$ in the tensor product $R \otimes_F M$, regarded as an $R$-algebra, the assertion is the equality, inside $R \otimes_F M$, $$\mathrm{algebraMap}_R\bigl(N_{(R \otimes_F M)/R}(z)\bigr) \;=\; \prod_{g \in \mathrm{Aut}_F(M)} \bigl(\mathrm{id}_R \otimes g\bigr)(z),$$ where $N_{(R \otimes_F M)/R}$ is Mathlib's algebra norm `Algebra.norm R` of the $R$-algebra $R \otimes_F M$ (the determinant of multiplication, computed with respect to an $R$-basis), the left-hand side is its image under the structure map $R \to R \otimes_F M$, and the product on the right runs over the finite group of $F$-algebra automorphisms $g$ of $M$, each acting through the $F$-algebra endomorphism `Algebra.TensorProduct.map (AlgHom.id F R) g` of $R \otimes_F M$, i.e. $r \otimes m \mapsto r \otimes g(m)$. For $R = F$ this is the classical formula $N_{M/F}(x) = \prod_{g} g(x)$; the statement here is its base change to an arbitrary commutative $F$-algebra $R$.
--
--   This is the norm-as-product-of-conjugates formula for a finite Galois extension, base changed along an arbitrary commutative $F$-algebra, reflecting the Galois splitting $M \otimes_F M \cong \prod_{g} M$. It is used in the analytic part of the development, where norms of elements of base-changed étale algebras over local and adelic rings must be expressed through their conjugates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv
    (F M : Type*) [Field F] [Field M] [Algebra F M] [FiniteDimensional F M] [IsGalois F M]
    (R : Type*) [CommRing R] [Algebra F R] (z : R ⊗[F] M) :
    algebraMap R (R ⊗[F] M) (Algebra.norm R z) =
      ∏ g : M ≃ₐ[F] M, Algebra.TensorProduct.map (AlgHom.id F R) (g : M →ₐ[F] M) z := by sorry
