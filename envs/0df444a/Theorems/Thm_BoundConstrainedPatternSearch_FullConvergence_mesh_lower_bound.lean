-- Prove2me | Theorems.Thm_BoundConstrainedPatternSearch_FullConvergence_mesh_lower_bound
-- name    : BoundConstrainedPatternSearch.FullConvergence.mesh_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:55.578871+00:00
-- url     : https://prove2.me/theorems/60d97151-7763-4f7f-b02a-8b6e8f4a5a90
-- title:
--   Corollary 4.4 — nonzero residual liminf forces a positive mesh bound
-- statement:
--   Let $\Omega=\{x\in\mathbb R^n:\ell\le x\le u\}$ with $\ell_j<u_j$ in every coordinate, allowing infinite bounds. Let $R=(x_k,\Delta_k,s_k,M_k,L_k)$ be a run of Algorithms 1–2, with fixed nonsingular basis $B$, finite nonsingular integer core family, diagonal $BM_k$, and the source's rational mesh updates. Write $P_\Omega$ for coordinatewise clamping, $g=\nabla f$ for the actual ambient gradient of $f:\mathbb R^n\to\mathbb R$, $q(x)=P_\Omega(x-g(x))-x$, and $S=L_\Omega(x_0)$. Assume ambient differentiability at every point of $S$ and continuity of $g$ restricted to $S$.
--
--   Assume $S$ is compact and $\liminf_{k\to\infty}\|q(x_k)\|\ne0$, with the liminf understood in the extended nonnegative sense. Then
--
--   $$
--   \exists\Delta_*>0\quad\forall k\ge0,\quad\Delta_k>\Delta_*.
--   $$
--
--   The strict lower bound covers the entire sequence, including its finite initial prefix. No bounded-column, strong-move or mesh-convergence premise is imposed. This is the mesh consequence of a residual staying away from zero.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors with coordinates 1 through n and possibly infinite box bounds → EuclideanSpace ℝ (Fin n), zero-based coordinates, EReal endpoints with lo j < hi j; reason: Reindexing preserves every finite dimension; strict gaps make the clamped value finite even for missing bounds
--   - encoding: Algorithms 1–2 and the finite feasible-core minimum rule → published GPSParams, GPSRun and IsGPSRun with actual column membership and an existential improving-core trigger; reason: The finite minimum improves exactly when a feasible core column improves; the empty-core trigger is false, and all rational updates, zero columns and diagonal cores are retained
--   - reading: f continuously differentiable on the closed feasible level set L_Ω(x₀) → ambient differentiability at every point of L_Ω(x₀) and continuity of the actual ambient gradient restricted to that set; reason: This specifies closed-set regularity even with empty interior, includes neighborhood-C¹ instances and requires no regularity elsewhere in Ω
--   - encoding: zero or nonzero liminf of the nonnegative residual norm → the arbitrarily-late small-value criterion, or its negation; reason: For nonnegative sequences this is equivalent to zero or nonzero extended liminf, including infinite liminf, and avoids default-valued real extrema
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 10 (PDF p. 12), Corollary 4.4

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_GPS
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
open LewisTorczon.BoundPS

namespace BoundConstrainedPatternSearch.FullConvergence

/-- Corollary 4.4, printed p. 10 (PDF p. 12). Negating the arbitrarily-late
small-value criterion expresses nonzero liminf for a nonnegative sequence, including
infinite liminf, without a default-valued real infimum. The lower bound is strict. -/
theorem mesh_lower_bound {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : LevelSetRegularity lo hi f (R.x 0))
    (hq : ¬ (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ k : ℕ, N ≤ k ∧ ‖projQ lo hi f (R.x k)‖ < ε)) :
    ∃ Δstar : ℝ, 0 < Δstar ∧ ∀ k, Δstar < R.Δ k := by sorry

end BoundConstrainedPatternSearch.FullConvergence
