-- Prove2me | Theorems.Thm_BoundConstrainedPatternSearch_FullConvergence_residual_tendsto_zero
-- name    : BoundConstrainedPatternSearch.FullConvergence.residual_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:42:51.065242+00:00
-- url     : https://prove2.me/theorems/3816e47e-d170-4a42-be0a-a16dd783e3a6
-- title:
--   Theorem 3.3 — the projected residual tends to zero
-- statement:
--   Let $\Omega=\{x\in\mathbb R^n:\ell\le x\le u\}$ with $\ell_j<u_j$ in every coordinate, allowing infinite bounds. Let $R=(x_k,\Delta_k,s_k,M_k,L_k)$ be a run of Algorithms 1–2, with fixed nonsingular basis $B$, finite nonsingular integer core family, diagonal $BM_k$, and the source's rational mesh updates. Write $P_\Omega$ for coordinatewise clamping, $g=\nabla f$ for the actual ambient gradient of $f:\mathbb R^n\to\mathbb R$, $q(x)=P_\Omega(x-g(x))-x$, and $S=L_\Omega(x_0)$. Assume ambient differentiability at every point of $S$ and continuity of $g$ restricted to $S$.
--
--   Assume $S$ is compact, the generating columns are uniformly bounded in Euclidean norm by one constant $C>0$, $\Delta_k\to0$, and all three strict Strong Hypotheses hold. Then the entire projected-residual sequence satisfies
--
--   $$
--   \lim_{k\to\infty}\|q(x_k)\|=
--   \lim_{k\to\infty}\|P_\Omega(x_k-\nabla f(x_k))-x_k\|=0.
--   $$
--
--   This is the complete Theorem 3.3 conclusion for every qualifying run. It does not assert convergence of the iterates to one point or global optimality. The feasible box can be unbounded, the objective nonconvex, and the finite dimension arbitrary, including zero. No derived descent, level-set trapping or residual convergence assertion is a field of the run.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors with coordinates 1 through n and possibly infinite box bounds → EuclideanSpace ℝ (Fin n), zero-based coordinates, EReal endpoints with lo j < hi j; reason: Reindexing preserves every finite dimension; strict gaps make the clamped value finite even for missing bounds
--   - encoding: Algorithms 1–2 and the finite feasible-core minimum rule → published GPSParams, GPSRun and IsGPSRun with actual column membership and an existential improving-core trigger; reason: The finite minimum improves exactly when a feasible core column improves; the empty-core trigger is false, and all rational updates, zero columns and diagonal cores are retained
--   - reading: f continuously differentiable on the closed feasible level set L_Ω(x₀) → ambient differentiability at every point of L_Ω(x₀) and continuity of the actual ambient gradient restricted to that set; reason: This specifies closed-set regularity even with empty interior, includes neighborhood-C¹ instances and requires no regularity elsewhere in Ω
--   - encoding: the three strict Strong Hypotheses on Bound Constrained Exploratory Moves → StrictStrongMoves retains selected-column membership and feasibility and requires strict comparison with every feasible core value on the improving-core trigger; reason: For the finite feasible core this is the printed strict minimum rule; no arbitrary value is assigned to an empty minimum
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 7 (PDF p. 9), Theorem 3.3

import Mathlib
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_StrictStrongMoves
open LewisTorczon.BoundPS
open scoped Topology

namespace BoundConstrainedPatternSearch.FullConvergence

/-- Theorem 3.3, printed p. 7 (PDF p. 9): the full projected-residual limit.
Regularity is confined to the initial feasible sublevel set; the strong comparison
is the literal printed strict one. No convergence conclusion is part of IsGPSRun. -/
theorem residual_tendsto_zero {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : LevelSetRegularity lo hi f (R.x 0)) (hbdd : BoundedCols R)
    (hΔ : Filter.Tendsto R.Δ Filter.atTop (nhds 0))
    (hstrong : StrictStrongMoves P lo hi f R) :
    Filter.Tendsto (fun k => ‖projQ lo hi f (R.x k)‖) Filter.atTop (nhds 0) := by sorry

end BoundConstrainedPatternSearch.FullConvergence
