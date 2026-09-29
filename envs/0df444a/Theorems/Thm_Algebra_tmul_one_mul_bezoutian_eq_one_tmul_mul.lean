-- Prove2me | Theorems.Thm_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul
-- name    : Algebra.tmul_one_mul_bezoutian_eq_one_tmul_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/f6b56d24-0e71-5330-99d9-5adba5bc89f5
-- title:
--   Balancedness of the Bezoutian of a square presentation
-- statement:
--   Let $R$ be a commutative ring, let $m$ be a natural number, write $P = R[x_0,\dots,x_{m-1}]$ for the polynomial ring `MvPolynomial (Fin m) R`, and let $f : \mathrm{Fin}\,m \to P$ be a family of $m$ polynomials. Let $a = (a_{ij})$ be an $m \times m$ family of elements of $P \otimes_R P$ satisfying the Bezout identity
--   $$f_i \otimes 1 - 1 \otimes f_i = \sum_{j} a_{ij}\,(x_j \otimes 1 - 1 \otimes x_j)$$
--   for every index $i$, where $x_j$ denotes `MvPolynomial.X j`. Put $A = P / (f_0,\dots,f_{m-1})$, the quotient of $P$ by the ideal spanned by the range of $f$, and let $\bar\Delta \in A \otimes_R A$ be the image of $\det(a_{ij})$ (the determinant of the matrix `Matrix.of a`) under the $R$-algebra map $A \otimes_R A \leftarrow P \otimes_R P$ induced on tensor products by the quotient map $P \to A$ in each factor. Then for every $s \in A$,
--   $$(s \otimes 1)\,\bar\Delta = (1 \otimes s)\,\bar\Delta$$
--   in $A \otimes_R A$.
--
--   This is the balancedness (or $A$-bilinearity) property of the Bezoutian of a square presentation $A = R[x_1,\dots,x_m]/(f_1,\dots,f_m)$: multiplication by the image of $\det(a_{ij})$ in $A \otimes_R A$ is insensitive to moving a scalar from the left factor to the right. It is used in the construction of the Scheja–Storch dual basis and trace form attached to a square presentation, being cited by [`Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed`](thm.html#Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed) and by [`Algebra.exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation`](thm.html#Algebra.exists_dual_bijective_mul_and_trace_eq_jacobianDet_mul_of_square_presentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_tmul_one_mul_bezoutian_eq_one_tmul_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.tmul_one_mul_bezoutian_eq_one_tmul_mul
    (R : Type*) [CommRing R] {m : ℕ} (f : Fin m → MvPolynomial (Fin m) R)
    (a : Fin m → Fin m → MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin m) R)
    (ha : ∀ i, f i ⊗ₜ[R] (1 : MvPolynomial (Fin m) R) - (1 : MvPolynomial (Fin m) R) ⊗ₜ[R] f i =
      ∑ j, a i j * (MvPolynomial.X j ⊗ₜ[R] 1 - 1 ⊗ₜ[R] MvPolynomial.X j))
    (s : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) :
    (s ⊗ₜ[R] (1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f))) *
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) =
      ((1 : MvPolynomial (Fin m) R ⧸ Ideal.span (Set.range f)) ⊗ₜ[R] s) *
        Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f)))
          (Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))) (Matrix.det (Matrix.of a)) := by sorry
