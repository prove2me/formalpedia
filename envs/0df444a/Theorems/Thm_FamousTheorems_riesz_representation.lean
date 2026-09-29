-- Prove2me | Theorems.Thm_FamousTheorems_riesz_representation
-- name    : FamousTheorems.riesz_representation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:23.37175+00:00
-- url     : https://prove2.me/theorems/25abe248-3d37-45c2-ab88-da02f528bade
-- title:
--   The Riesz representation theorem (Hilbert spaces)
-- statement:
--   **The Riesz representation theorem (Hilbert spaces).** Let $E$ be a Hilbert space over $\mathbb R$ or $\mathbb C$. The map $x\mapsto\langle x,\cdot\rangle$ is a conjugate-linear isometric isomorphism from $E$ onto its dual $E^*$ of continuous linear functionals. So every continuous linear functional is $y\mapsto\langle x,y\rangle$ for a unique $x$, with $\|x\|$ equal to the functional's norm.
--
--   It identifies a Hilbert space with its own dual. It is behind adjoint operators, the Lax–Milgram theorem, weak solutions of PDE, and the Radon–Nikodym theorem via von Neumann's proof.
--
--   **Formalization note.** Mathlib's `InnerProductSpace.toDual 𝕜 E : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E`. The statement asserts that a conjugate-linear isometric equivalence exists and that it acts by the inner product, `Φ x y = ⟪x, y⟫`, which holds by definition (`InnerProductSpace.toDual_apply_apply`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `InnerProductSpace.toDual`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riesz_representation (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    ∃ Φ : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E, ∀ x y : E, Φ x y = inner 𝕜 x y := by sorry

end FamousTheorems
