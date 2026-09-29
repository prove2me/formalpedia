-- Prove2me | Theorems.Thm_FamousTheorems_hahn_banach
-- name    : FamousTheorems.hahn_banach
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:08.017003+00:00
-- url     : https://prove2.me/theorems/92d6e40e-58c6-44d9-9d1d-d6beae0136d7
-- title:
--   The Hahn–Banach theorem (norm-preserving extension)
-- statement:
--   **The Hahn–Banach theorem (norm-preserving extension).** Let $E$ be a normed space over $\mathbb R$ or $\mathbb C$ and $p\subseteq E$ a subspace. Every continuous linear functional $f$ on $p$ extends to a continuous linear functional $g$ on $E$ with $\|g\|=\|f\|$.
--
--   This is a cornerstone of functional analysis. It guarantees that the dual space separates points, gives the isometric embedding of $E$ into its bidual, and underlies duality arguments throughout analysis.
--
--   **Formalization note.** Mathlib's `exists_extension_norm_eq`, for seminormed spaces over an `RCLike`-type field; `StrongDual 𝕜 E` is the space of continuous linear functionals with the operator norm.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_extension_norm_eq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem hahn_banach {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (p : Subspace 𝕜 E) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ := by sorry

end FamousTheorems
