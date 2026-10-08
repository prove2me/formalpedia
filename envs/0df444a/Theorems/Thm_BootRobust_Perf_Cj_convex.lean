-- Prove2me | Theorems.Thm_BootRobust_Perf_Cj_convex
-- name    : BootRobust.Perf.Cj_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:12.713929+00:00
-- url     : https://prove2.me/theorems/0773d200-366f-43d8-ac08-37fe93d30614
-- title:
--   Proof of Theorem 6, p. 15 — each set C_j = {D ∈ D^j_n : E^{n,j}_D > c̄} is convex
-- statement:
--   Let $n\ge 1$, $k\ge 1$, let $N^0,N^1,\dots$ be neighbourhoods in $\Omega_n$, $w>0$ weights and $\ell$ losses. For every threshold $\bar c\in[-\infty,+\infty]$ and every $j$, the set
--   $$\mathcal C_j=\big\{D\in\mathcal D^j_n:\ E^{n,j}_D>\bar c\big\}$$
--   is convex.
--
--   On $\mathcal D^j_n$ the partial estimator is a ratio of linear functions with positive denominator, so $\mathcal C_j$ is cut out by a linear inequality. Convexity is what allows Csiszár's inequality (Theorem 5) to be applied to each $\mathcal C_j$.
--
--   **Formalization Note** The page calls $\mathcal C_j$ a convex polyhedron; only convexity is formalized, as it is all Theorem 5 needs. The threshold is arbitrary, including $\pm\infty$; in the proof it is the robust budget.
-- source:
--   Bertsimas and Van Parys, Bootstrap robust prescriptive analytics, arXiv:1711.09974v2, proof of Theorem 6, p. 15, "Each of the partial sets C_j is a convex polyhedron."

import Mathlib
import Definitions.Def_BootRobust_Perf_Setting

namespace BootRobust.Perf

/-- Proof of Theorem 6, p. 15: each set `C_j = {D ∈ D^j_n : E^{n,j}_D > c̄}` is convex, for any
threshold `c̄ ∈ EReal`. -/
theorem Cj_convex {ι : Type*} [Fintype ι] [DecidableEq ι] (n k : ℕ) (hn : 1 ≤ n)
    (hk : 1 ≤ k) (N : ℕ → Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 < w i) (ℓ : ι → ℝ)
    (cbar : EReal) (j : ℕ) :
    Convex ℝ (Cj n k N w ℓ cbar j) := by sorry

end BootRobust.Perf
