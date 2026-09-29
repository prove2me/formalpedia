-- Prove2me | Theorems.Thm_FamousTheorems_convex_local_min_is_global_7a
-- name    : FamousTheorems.convex_local_min_is_global_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:03.342368+00:00
-- url     : https://prove2.me/theorems/778e2156-2565-4dc2-9555-cc2a537b9950
-- title:
--   A local minimum of a convex function is a global minimum
-- statement:
--   **A local minimum of a convex function is a global minimum.** Let $E$ be a real normed space, $s\subseteq E$, and $f:E\to\mathbb R$ convex on $s$. If $a\in s$ is a local minimum of $f$ on $s$, then $f(a)\le f(x)$ for every $x\in s$.
--
--   This is why convex optimization problems are tractable: any local search method that finds a local minimum has found a global one. The proof restricts $f$ to the segment from $a$ to $x$ and uses convexity to compare $f(x)$ with values of $f$ near $a$.
--
--   **Formalization note.** Mathlib's `IsMinOn.of_isLocalMinOn_of_convexOn`, specialised to real-valued functions on a real normed space. Mathlib states it for ordered modules as codomains. `IsLocalMinOn f s a` means that $f(a)\le f(x)$ for all $x\in s$ in some neighbourhood of $a$, and `IsMinOn f s a` means that this holds for all $x\in s$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsMinOn.of_isLocalMinOn_of_convexOn`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem convex_local_min_is_global_7a {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ} {a : E} (ha : a ∈ s)
    (hmin : IsLocalMinOn f s a) (hf : ConvexOn ℝ s f) : IsMinOn f s a := by sorry

end FamousTheorems
