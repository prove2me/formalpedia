-- Prove2me | Theorems.Thm_BurauFaithful_spec_reduced_coxeter
-- name    : BurauFaithful.spec_reduced_coxeter
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-29T17:30:01.790751+00:00
-- url     : https://prove2.me/theorems/05b9fffb-509e-4647-b662-ee52c7922209
-- title:
--   Coxeter-Moser relations for the specialized reduced Burau generators $A,B\in\mathrm{SL}(2,\mathbb Z)$
-- statement:
--   The specialization at $t=-1$ of the 2-dimensional reduced Burau representation sends the two generators $\sigma_1,\sigma_2$ of $B_3$ to the integral matrices
--
--   $$A=\begin{pmatrix}1&-1\\0&1\end{pmatrix},\qquad B=\begin{pmatrix}2&-1\\1&0\end{pmatrix},$$
--
--   of determinant $1$, i.e. to elements of the homogeneous modular group $M_2=\mathrm{SL}(2,\mathbb Z)$. This theorem records that these two matrices satisfy the defining relations of the Coxeter-Moser presentation of $M_2$ (Moser-Coxeter 1964, p. 85; Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, §3.3, pp. 129-130):
--
--   $$ABA=BAB,\qquad (ABA)^4=1,\qquad \det A=\det B=1,$$
--
--   so that the assignment $s_1\mapsto A$, $s_2\mapsto B$ is a well-defined homomorphism
--   $\langle s_1,s_2\mid s_1s_2s_1=s_2s_1s_2,\ (s_1s_2s_1)^4=1\rangle\to M_2$. It also records $(AB)^6=1$, the image of $\Delta^4=(\sigma_1\sigma_2)^6$, the generator of the kernel of the specialization.
--
--   All five statements are finite computations over the integers.
--
--   **Formalization Note** The matrices are written as matrix literals `!![...; ...]` over `ℤ`, and the conjunction is decided by computation.
-- source:
--   C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups*, 2nd ed., Springer 1964, p. 85 (presentation of the homogeneous modular group); J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, Theorem 3.15, pp. 129-130.

import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

theorem BurauFaithful.spec_reduced_coxeter :
    ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0] * !![1, -1; 0, 1] =
        !![2, -1; 1, 0] * !![1, -1; 0, 1] * !![2, -1; 1, 0]) ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0] * !![1, -1; 0, 1]) ^ 4 = 1 ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)).det = 1 ∧
      (!![2, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 ∧
      ((!![1, -1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![2, -1; 1, 0]) ^ 6 = 1 := by sorry
