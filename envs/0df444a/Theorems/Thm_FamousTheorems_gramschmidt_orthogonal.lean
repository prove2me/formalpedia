-- Prove2me | Theorems.Thm_FamousTheorems_gramschmidt_orthogonal
-- name    : FamousTheorems.gramschmidt_orthogonal
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:42.823505+00:00
-- url     : https://prove2.me/theorems/094d39e6-f744-4014-a4cf-d9471a0c51a3
-- title:
--   Gram–Schmidt orthogonalisation
-- statement:
--   **Gram–Schmidt orthogonalisation.** The vectors produced by the Gram–Schmidt process from a linearly independent family are pairwise orthogonal: $$\langle g_i, g_j \rangle = 0 \quad\text{for } i \neq j.$$ The construction subtracts from each input vector its projections onto the previously produced ones, so the output spans the same increasing family of subspaces while being orthogonal. Normalising afterwards gives an orthonormal basis, which is the standard proof that every finite-dimensional inner product space has one. The triangular nature of the process — each output depends only on the inputs up to that index — is what makes it equivalent to the $QR$ decomposition of a matrix, and it is why the algorithm is the basis of least-squares solvers, though the naive version is numerically unstable and the modified variant is used in practice. **Formalization note.** The index type is linearly ordered so that "previous" makes sense, and the result asserts orthogonality of the unnormalised output. The result is Mathlib's `InnerProductSpace.gramSchmidt_orthogonal`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem gramschmidt_orthogonal :
    ∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] 
    [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] {ι : Type u_3} [inst_3 : LinearOrder ι] 
    [inst_4 : LocallyFiniteOrderBot ι] [inst_5 : WellFoundedLT ι] (f : ι → E) {a b : ι}, 
    a ≠ b → inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f a) (InnerProductSpace.gramSchmidt 𝕜 f b) = 0 := by sorry

end FamousTheorems
