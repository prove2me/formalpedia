-- Prove2me | Theorems.Thm_FamousTheorems_simultaneous_diagonalization_commuting_selfadjoint_6c
-- name    : FamousTheorems.simultaneous_diagonalization_commuting_selfadjoint_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:34.278694+00:00
-- url     : https://prove2.me/theorems/8ae6f627-aed4-4d17-9c9b-6000474d79fc
-- title:
--   Simultaneous diagonalisation of commuting self-adjoint operators
-- statement:
--   **Simultaneous diagonalisation of commuting self-adjoint operators.** Let $A$ and $B$ be commuting self-adjoint operators on a finite-dimensional real or complex inner product space $E$. Then $E$ is the internal direct sum of the joint eigenspaces
--   $$E_{\alpha,\beta}=\ker(A-\beta)\cap\ker(B-\alpha),\qquad(\alpha,\beta)\in\mathbb K\times\mathbb K.$$
--
--   So $A$ and $B$ have a common orthonormal eigenbasis. This is the finite-dimensional case of the spectral theorem for commuting families of normal operators, and in quantum mechanics it is the statement that commuting observables can be measured simultaneously.
--
--   **Formalization note.** Mathlib's `LinearMap.IsSymmetric.directSum_isInternal_of_commute`. `DirectSum.IsInternal` says that the canonical map from the external direct sum of the subspaces to $E$ is bijective. In the index pair `i`, `i.2` is the eigenvalue of $A$ and `i.1` the eigenvalue of $B$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LinearMap.IsSymmetric.directSum_isInternal_of_commute`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem simultaneous_diagonalization_commuting_selfadjoint_6c {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    DirectSum.IsInternal fun i : 𝕜 × 𝕜 => Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1 := by sorry

end FamousTheorems
