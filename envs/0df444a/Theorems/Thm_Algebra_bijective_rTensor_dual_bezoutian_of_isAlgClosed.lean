-- Prove2me | Theorems.Thm_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed
-- name    : Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/5cedbb77-da5e-502e-8382-4395c028a602
-- title:
--   Scheja–Storch bijectivity over an algebraically closed field
-- statement:
--   Let $K$ be an algebraically closed field, let $m\in\mathbb{N}$, and let $g\colon \mathrm{Fin}\,m \to K[X_0,\dots,X_{m-1}]$ be a family of $m$ polynomials in $m$ variables such that the quotient algebra $A := K[X]/(g_0,\dots,g_{m-1})$, formed as the quotient by the ideal spanned by the range of $g$, is a finite $K$-module. Let $b$ be an $m\times m$ matrix of elements $b_{ij}$ of $K[X]\otimes_K K[X]$ satisfying the Bézout identity
--   $$g_i\otimes 1 - 1\otimes g_i = \sum_j b_{ij}\,(X_j\otimes 1 - 1\otimes X_j)\qquad\text{for all } i .$$
--   Write $\bar\Delta\in A\otimes_K A$ for the image of $\det b$ under the algebra map $A\otimes_K A$ induced by the two quotient maps $K[X]\to A$. The assertion is that the $K$-linear map
--   $$\operatorname{Hom}_K(A,K)\longrightarrow A,\qquad \varphi\longmapsto (\varphi\otimes \mathrm{id}_A)(\bar\Delta),$$
--   where the right-hand side is read in $A$ via the canonical isomorphism $K\otimes_K A\cong A$, is bijective.
--
--   This is the bijectivity half of the Scheja–Storch construction: the Bézoutian determinant $\bar\Delta$ of a finite square presentation induces an isomorphism between the $K$-dual of $A$ and $A$ itself, which is what makes $A$ a Frobenius algebra over $K$. It is the algebraically closed case, from which the statement for a general base is obtained in [`Algebra.bijective_rTensor_dual_bezoutian_of_square_presentation`](thm.html#Algebra.bijective_rTensor_dual_bezoutian_of_square_presentation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_bijective_rTensor_dual_bezoutian_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem Algebra.bijective_rTensor_dual_bezoutian_of_isAlgClosed
    (K : Type*) [Field K] [IsAlgClosed K] {m : ℕ} (g : Fin m → MvPolynomial (Fin m) K)
    [Module.Finite K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))]
    (b : Fin m → Fin m → MvPolynomial (Fin m) K ⊗[K] MvPolynomial (Fin m) K)
    (hb : ∀ i, g i ⊗ₜ[K] (1 : MvPolynomial (Fin m) K) - (1 : MvPolynomial (Fin m) K) ⊗ₜ[K] g i =
      ∑ j, b i j * (MvPolynomial.X j ⊗ₜ[K] 1 - 1 ⊗ₜ[K] MvPolynomial.X j)) :
    Function.Bijective (fun φ : Module.Dual K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) =>
      TensorProduct.lid K (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g))
        (LinearMap.rTensor (MvPolynomial (Fin m) K ⧸ Ideal.span (Set.range g)) φ
          (Algebra.TensorProduct.map
              (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g))) (Ideal.Quotient.mkₐ K (Ideal.span (Set.range g)))
            (Matrix.det (Matrix.of b))))) := by sorry
