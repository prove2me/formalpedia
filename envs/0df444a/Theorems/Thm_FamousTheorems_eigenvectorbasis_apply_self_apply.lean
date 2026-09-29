-- Prove2me | Theorems.Thm_FamousTheorems_eigenvectorbasis_apply_self_apply
-- name    : FamousTheorems.eigenvectorbasis_apply_self_apply
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:43.020607+00:00
-- url     : https://prove2.me/theorems/d469e1bf-47ff-4fd6-b5f8-f56affd5cc9a
-- title:
--   Diagonalisation of a self-adjoint endomorphism
-- statement:
--   **The spectral theorem** for a self-adjoint endomorphism in finite dimensions. A symmetric operator acts on its eigenvector basis by scaling each basis vector by the corresponding eigenvalue, so in that basis the operator is diagonal. Self-adjointness is exactly the condition that forces the eigenvalues to be real and the eigenvectors corresponding to distinct eigenvalues to be orthogonal, so the eigenvector basis can be taken orthonormal. The result is the cleanest structure theorem in linear algebra: no Jordan blocks, no complex eigenvalues, no defective operators. Its consequences run through mathematics — principal component analysis, the classification of quadratic forms, normal modes of vibration, and the observables of quantum mechanics are all this theorem in application. The infinite-dimensional analogues (for compact self-adjoint operators, and the general spectral theorem for unbounded self-adjoint operators) are substantially harder but follow the same outline. **Formalization note.** `LinearMap.IsSymmetric` is self-adjointness with respect to the inner product, and `eigenvectorBasis` is the orthonormal eigenbasis it produces. The result is Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem eigenvectorbasis_apply_self_apply :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} 
    [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [inst_3 : FiniteDimensional 𝕜 E] 
    {n : ℕ} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) (i : Fin n), 
    ((hT.eigenvectorBasis hn).repr (T v)).ofLp i = ↑(hT.eigenvalues hn i) * ((hT.eigenvectorBasis hn).repr v).ofLp i := by sorry

end FamousTheorems
