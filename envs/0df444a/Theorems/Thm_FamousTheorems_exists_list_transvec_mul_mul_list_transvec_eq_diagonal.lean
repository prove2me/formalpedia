-- Prove2me | Theorems.Thm_FamousTheorems_exists_list_transvec_mul_mul_list_transvec_eq_diagonal
-- name    : FamousTheorems.exists_list_transvec_mul_mul_list_transvec_eq_diagonal
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:35.424864+00:00
-- url     : https://prove2.me/theorems/694f4302-930c-4075-9469-4e6c5a9b60dc
-- title:
--   Gaussian elimination
-- statement:
--   **Gaussian elimination**, in transvection form. Every square matrix over a field can be reduced to a diagonal matrix by multiplying on the left and right by products of transvections (elementary row and column operations): $$L\,M\,L' = \operatorname{diag}(D).$$ Transvections are the shear matrices $I + c\,E_{ij}$ with $i \neq j$; each corresponds to adding a multiple of one row (or column) to another, which is exactly the elementary operation performed at each step of the algorithm. The theorem is the statement that the algorithm always terminates in diagonal form. Beyond being the practical method for solving linear systems and inverting matrices, it is a structural fact: transvections generate the special linear group, so the theorem says $\mathrm{SL}_n$ acts on matrices with diagonal orbit representatives. This is the starting point for Smith normal form and for the stability results of algebraic K-theory. **Formalization note.** `Matrix.TransvectionStruct` bundles the data of a transvection and `toMatrix` realises it; the products are taken over lists. The result is Mathlib's `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal :
    ∀ {n : Type u_1} {𝕜 : Type u_2} [inst : Field 𝕜] 
    [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n 𝕜), 
    ∃ L L' D, 
    (List.map Matrix.TransvectionStruct.toMatrix L).prod * M * (List.map Matrix.TransvectionStruct.toMatrix L').prod = 
    Matrix.diagonal D := by sorry

end FamousTheorems
