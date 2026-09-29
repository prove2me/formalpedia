-- Prove2me | Theorems.Thm_FamousTheorems_hellinger_toeplitz
-- name    : FamousTheorems.hellinger_toeplitz
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:34.353018+00:00
-- url     : https://prove2.me/theorems/52c9c399-79df-479f-a8d5-d8554450ba92
-- title:
--   The Hellinger–Toeplitz theorem
-- statement:
--   **The Hellinger–Toeplitz theorem.** A linear operator $T$ defined on the whole of a Hilbert space and symmetric, i.e. $\langle Tx,y\rangle=\langle x,Ty\rangle$ for all $x,y$, is automatically bounded (continuous).
--
--   So the unbounded self-adjoint operators of quantum mechanics (position, momentum, Schrödinger operators) cannot be defined on the whole space. This is why unbounded operators have to come with dense domains, and why spectral theory for them requires extra care.
--
--   **Formalization note.** Mathlib's `LinearMap.IsSymmetric.continuous`, for complete inner product spaces over `ℝ` or `ℂ` (`RCLike`). The proof applies the closed graph theorem.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `LinearMap.IsSymmetric.continuous`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hellinger_toeplitz {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) : Continuous T := by sorry

end FamousTheorems
