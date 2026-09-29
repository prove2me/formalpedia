-- Prove2me | Theorems.Thm_FamousTheorems_tomatrix_comp
-- name    : FamousTheorems.tomatrix_comp
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:34.881021+00:00
-- url     : https://prove2.me/theorems/88786a74-8b31-40e0-a996-ed5dd8d95a43
-- title:
--   Change of coordinates for a bilinear form
-- statement:
--   **Change of coordinates for a bilinear form.** Precomposing a bilinear form with linear maps transforms its matrix by $$M(B \circ (l, r)) = L^{\mathsf T}\, M(B)\, R,$$ where $L$ and $R$ are the matrices of the two maps. Bilinear forms transform *congruently* — with $L^{\mathsf T}$ on the left — rather than by similarity. That single difference separates the theory of bilinear and quadratic forms from the theory of linear operators: the invariants are rank and signature rather than eigenvalues, and the classification is Sylvester's law of inertia rather than Jordan form. In the symmetric case with $l = r$ this is the congruence $B \mapsto L^{\mathsf T} B L$ used to diagonalise quadratic forms. **Formalization note.** `LinearMap.BilinForm.toMatrix` takes a basis and returns the Gram matrix of the form. The result is Mathlib's `LinearMap.BilinForm.toMatrix_comp`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tomatrix_comp :
    ∀ {R₁ : Type u_1} {M₁ : Type u_2} [inst : CommSemiring R₁] 
    [inst_1 : AddCommMonoid M₁] [inst_2 : Module R₁ M₁] {n : Type u_3} {o : Type u_4} [inst_3 : Fintype n] 
    [inst_4 : Fintype o] [inst_5 : DecidableEq n] (b : Module.Basis n R₁ M₁) {M₂' : Type u_5} [inst_6 : AddCommMonoid M₂'] 
    [inst_7 : Module R₁ M₂'] (c : Module.Basis o R₁ M₂') [inst_8 : DecidableEq o] (B : LinearMap.BilinForm R₁ M₁) 
    (l r : M₂' →ₗ[R₁] M₁), 
    (LinearMap.BilinForm.toMatrix c) (B.comp l r) = 
    ((LinearMap.toMatrix c b) l).transpose * (LinearMap.BilinForm.toMatrix b) B * (LinearMap.toMatrix c b) r := by sorry

end FamousTheorems
