-- Prove2me | Theorems.Thm_FamousTheorems_basis_tomatrix_mul_linearmap_tomatrix_mul_basis_tomatrix
-- name    : FamousTheorems.basis_tomatrix_mul_linearmap_tomatrix_mul_basis_tomatrix
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:32.185358+00:00
-- url     : https://prove2.me/theorems/b4dacaaa-4f84-4374-a10e-094cd23612cf
-- title:
--   Change of basis for a linear map
-- statement:
--   **Change of basis.** If a linear map is represented by a matrix with respect to one pair of bases, its matrix with respect to another pair is obtained by conjugating with the change-of-basis matrices: $$P\,A\,Q = A',$$ where $P$ and $Q$ are the transition matrices on the target and source. The matrix of a linear map is not an invariant of the map — it depends on the bases chosen — and this identity says precisely how it depends on them. What survives are the conjugation-invariant quantities: rank, determinant, trace, characteristic polynomial, eigenvalues. In the square case with a single basis it specialises to similarity $A' = P A P^{-1}$, and the classification of matrices up to similarity is the theory of canonical forms. **Formalization note.** `Module.Basis.toMatrix` produces the transition matrix between two bases and `LinearMap.toMatrix b c f` the matrix of `f` from basis `b` to basis `c`. The result is Mathlib's `basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem basis_tomatrix_mul_linearmap_tomatrix_mul_basis_tomatrix :
    ∀ {ι : Type u_1} {ι' : Type u_2} {κ : Type u_3} 
    {κ' : Type u_4} {R : Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M] 
    {N : Type u_7} [inst_3 : AddCommMonoid N] [inst_4 : Module R N] (b : Module.Basis ι R M) (b' : Module.Basis ι' R M) 
    (c : Module.Basis κ R N) (c' : Module.Basis κ' R N) (f : M →ₗ[R] N) [inst_5 : Fintype ι'] [inst_6 : Finite κ] 
    [inst_7 : Fintype ι] [inst_8 : Fintype κ'] [inst_9 : DecidableEq ι] [inst_10 : DecidableEq ι'], 
    c.toMatrix ⇑c' * (LinearMap.toMatrix b' c') f * b'.toMatrix ⇑b = (LinearMap.toMatrix b c) f := by sorry

end FamousTheorems
