-- Prove2me | Theorems.Thm_FamousTheorems_fredholm_alternative
-- name    : FamousTheorems.fredholm_alternative
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:27.090458+00:00
-- url     : https://prove2.me/theorems/a5464958-7943-4f6b-9d38-29d60e7abbc0
-- title:
--   The Fredholm alternative
-- statement:
--   **The Fredholm alternative.** Let $T$ be a compact operator on a Banach space $X$ over a nontrivially normed field, and $\mu\neq0$ a scalar. Then either $\mu$ is an eigenvalue of $T$ (so $Tx=\mu x$ has a nonzero solution), or $\mu$ lies in the resolvent set of $T$ (so $T-\mu$ is invertible with bounded inverse, and $Tx-\mu x=y$ has a unique solution for every $y$).
--
--   In particular every nonzero point of the spectrum of a compact operator is an eigenvalue. This is the basic solvability theory for integral equations of the second kind and for elliptic boundary value problems, and it is the first step of the spectral theory of compact operators.
--
--   **Formalization note.** Mathlib's `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`. `Module.End.HasEigenvalue` refers to `T` viewed as a linear map, and `resolventSet 𝕜 T` is the set of scalars $\mu$ for which `algebraMap 𝕜 _ μ - T` is a unit in the algebra of bounded operators.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsCompactOperator.hasEigenvalue_or_mem_resolventSet`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem fredholm_alternative {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    {T : X →L[𝕜] X} (hT : IsCompactOperator T) {μ : 𝕜} (hμ : μ ≠ 0) :
    Module.End.HasEigenvalue (T : X →ₗ[𝕜] X) μ ∨ μ ∈ resolventSet 𝕜 T := by sorry

end FamousTheorems
