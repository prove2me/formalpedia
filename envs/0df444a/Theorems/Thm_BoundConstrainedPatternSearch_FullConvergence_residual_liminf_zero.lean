-- Prove2me | Theorems.Thm_BoundConstrainedPatternSearch_FullConvergence_residual_liminf_zero
-- name    : BoundConstrainedPatternSearch.FullConvergence.residual_liminf_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:19.591541+00:00
-- url     : https://prove2.me/theorems/256ff8fe-755c-4cca-a8b6-c3b4168eff92
-- title:
--   Theorem 3.2 — projected-residual liminf is zero
-- statement:
--   Let $\Omega=\{x\in\mathbb R^n:\ell\le x\le u\}$ with $\ell_j<u_j$ in every coordinate, allowing infinite bounds. Let $R=(x_k,\Delta_k,s_k,M_k,L_k)$ be a run of Algorithms 1–2, with fixed nonsingular basis $B$, finite nonsingular integer core family, diagonal $BM_k$, and the source's rational mesh updates. Write $P_\Omega$ for coordinatewise clamping, $g=\nabla f$ for the actual ambient gradient of $f:\mathbb R^n\to\mathbb R$, $q(x)=P_\Omega(x-g(x))-x$, and $S=L_\Omega(x_0)$. Assume ambient differentiability at every point of $S$ and continuity of $g$ restricted to $S$.
--
--   If $S$ is compact, then
--
--   $$
--   \liminf_{k\to\infty}\|q(x_k)\|=0,
--   \quad\text{equivalently}\quad
--   \forall\varepsilon>0\ \forall N\in\mathbb N\ \exists k\ge N:\ \|q(x_k)\|<\varepsilon.
--   $$
--
--   This is the source's subsequential stationarity result and a dependency of the full-limit goal. It assumes neither bounded generating columns, strict strong moves nor $\Delta_k\to0$.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors with coordinates 1 through n and possibly infinite box bounds → EuclideanSpace ℝ (Fin n), zero-based coordinates, EReal endpoints with lo j < hi j; reason: Reindexing preserves every finite dimension; strict gaps make the clamped value finite even for missing bounds
--   - encoding: Algorithms 1–2 and the finite feasible-core minimum rule → published GPSParams, GPSRun and IsGPSRun with actual column membership and an existential improving-core trigger; reason: The finite minimum improves exactly when a feasible core column improves; the empty-core trigger is false, and all rational updates, zero columns and diagonal cores are retained
--   - reading: f continuously differentiable on the closed feasible level set L_Ω(x₀) → ambient differentiability at every point of L_Ω(x₀) and continuity of the actual ambient gradient restricted to that set; reason: This specifies closed-set regularity even with empty interior, includes neighborhood-C¹ instances and requires no regularity elsewhere in Ω
--   - encoding: zero or nonzero liminf of the nonnegative residual norm → the arbitrarily-late small-value criterion, or its negation; reason: For nonnegative sequences this is equivalent to zero or nonzero extended liminf, including infinite liminf, and avoids default-valued real extrema
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 7 (PDF p. 9), Theorem 3.2

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_GPS
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
open LewisTorczon.BoundPS

namespace BoundConstrainedPatternSearch.FullConvergence

/-- Theorem 3.2, printed p. 7 (PDF p. 9): arbitrarily late small residuals.
No bounded-column, strong-move or mesh-convergence hypothesis is imposed. -/
theorem residual_liminf_zero {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : LevelSetRegularity lo hi f (R.x 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ k : ℕ, N ≤ k ∧ ‖projQ lo hi f (R.x k)‖ < ε := by sorry

end BoundConstrainedPatternSearch.FullConvergence
