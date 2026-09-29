-- Prove2me | Theorems.Thm_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det
-- name    : AutomorphicForm.det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6ca46a46-9a55-526e-8448-3f3188707f31
-- title:
--   Gram determinant of the archimedean trace form on M_m(L⊗_K K_∞)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\iota$, $\kappa$, $m$ be finite index types with decidable equality. Let $b=(b_i)_{i\in\iota}$ be a basis of $K$ as a $\mathbb{Q}$-vector space and let $x=(x_i)_{i\in\kappa}$ be a family of $m\times m$ matrices over $L$. Equip the infinite adele ring $K_\infty$ of $K$ with the $\mathbb{R}$-algebra structure obtained by composing $\operatorname{algebraMap}\ \mathbb{R}\to$ the mixed space of $K$ with the inverse of the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K`, and equip $E=L\otimes_K K_\infty$ with the $\mathbb{R}$-algebra structure obtained by composing this with the right inclusion $K_\infty\to L\otimes_K K_\infty$. For $p\in\iota\times\kappa$ write $X_p$ for the matrix obtained from $x_{p.2}$ by applying entrywise the map $l\mapsto l\otimes_K \operatorname{algebraMap}(b_{p.1})$, a matrix over $E$. The assertion is that the determinant of the $(\iota\times\kappa)$-indexed matrix with $(p,q)$ entry $\operatorname{Tr}_{E/\mathbb{R}}\bigl(\operatorname{tr}(X_pX_q)\bigr)$ equals the image in $\mathbb{R}$ of the rational number $\operatorname{disc}_{\mathbb{Q}}(b)^{\,\lvert\kappa\rvert}\cdot N_{K/\mathbb{Q}}\bigl(\det(\operatorname{Tr}_{L/K}\operatorname{tr}(x_ix_j))_{i,j\in\kappa}\bigr)$.
--
--   This is the archimedean Gram determinant computation for the trace form $(X,Y)\mapsto \operatorname{Tr}_{E/\mathbb{R}}\operatorname{tr}(XY)$ on $m\times m$ matrices over $E=L\otimes_K K_\infty$, evaluated on the family obtained by scaling a family over $L$ by a $\mathbb{Q}$-basis of $K$: the answer is a power of the discriminant of that basis times the norm of the determinant of the corresponding $K$-valued Gram matrix. It is used in the volume computation for the parallelepiped spanned by such a family against an integral basis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.det_trace_real_matrix_trace_map_tmul_mul_eq_discr_pow_mul_norm_det
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {ι κ m : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype m] [DecidableEq m]
    (b : Module.Basis ι ℚ K) (x : κ → Matrix m m L) :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (Matrix.of fun p q : ι × κ =>
      Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K)
        (Matrix.trace
          ((x p.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b p.1)) *
            (x q.2).map (fun l : L => l ⊗ₜ[K] algebraMap K (InfiniteAdeleRing K) (b q.1))))).det =
      ((Algebra.discr ℚ b ^ Fintype.card κ *
          Algebra.norm ℚ (Matrix.of fun i j : κ => Algebra.trace K L (Matrix.trace (x i * x j))).det : ℚ) : ℝ) := by sorry
