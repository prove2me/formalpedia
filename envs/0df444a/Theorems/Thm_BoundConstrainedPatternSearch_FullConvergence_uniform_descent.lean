-- Prove2me | Theorems.Thm_BoundConstrainedPatternSearch_FullConvergence_uniform_descent
-- name    : BoundConstrainedPatternSearch.FullConvergence.uniform_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:41:17.092624+00:00
-- url     : https://prove2.me/theorems/05210d54-3b9a-456d-8fd0-411826f2f4f2
-- title:
--   Proposition 4.3 — uniform acceptability and sufficient decrease
-- statement:
--   Let $\Omega=\{x\in\mathbb R^n:\ell\le x\le u\}$ with $\ell_j<u_j$ in every coordinate, allowing infinite bounds. Let $R=(x_k,\Delta_k,s_k,M_k,L_k)$ be a run of Algorithms 1–2, with fixed nonsingular basis $B$, finite nonsingular integer core family, diagonal $BM_k$, and the source's rational mesh updates. Write $P_\Omega$ for coordinatewise clamping, $g=\nabla f$ for the actual ambient gradient of $f:\mathbb R^n\to\mathbb R$, $q(x)=P_\Omega(x-g(x))-x$, and $S=L_\Omega(x_0)$. Assume ambient differentiability at every point of $S$ and continuity of $g$ restricted to $S$.
--
--   Assume $S$ is compact. Both conclusions hold, with the additional hypotheses attached only to the second:
--
--   1. For every $\eta>0$ there is $\delta>0$, independent of $k$, such that
--      $$\Delta_k<\delta,\ \|q(x_k)\|>\eta\ \Longrightarrow\ f(x_k+s_k)<f(x_k)\ \text{and}\ x_k+s_k\in\Omega.$$
--   2. If one positive constant bounds the norms of every generating column at every iteration and the strict Strong Hypotheses hold, then for every $\eta>0$ there are $\delta>0$ and $\sigma>0$, independent of $k$, such that
--      $$\Delta_k<\delta,\ \|q(x_k)\|>\eta\ \Longrightarrow\ f(x_{k+1})\le f(x_k)-\sigma\|q(x_k)\|\|s_k\|.$$
--
--   This single item retains the complete two-part proposition. The second estimate supplies quantitative decrease away from stationarity; neither that estimate nor any residual convergence property is assumed in the run model.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors with coordinates 1 through n and possibly infinite box bounds → EuclideanSpace ℝ (Fin n), zero-based coordinates, EReal endpoints with lo j < hi j; reason: Reindexing preserves every finite dimension; strict gaps make the clamped value finite even for missing bounds
--   - encoding: Algorithms 1–2 and the finite feasible-core minimum rule → published GPSParams, GPSRun and IsGPSRun with actual column membership and an existential improving-core trigger; reason: The finite minimum improves exactly when a feasible core column improves; the empty-core trigger is false, and all rational updates, zero columns and diagonal cores are retained
--   - reading: f continuously differentiable on the closed feasible level set L_Ω(x₀) → ambient differentiability at every point of L_Ω(x₀) and continuity of the actual ambient gradient restricted to that set; reason: This specifies closed-set regularity even with empty interior, includes neighborhood-C¹ instances and requires no regularity elsewhere in Ω
--   - encoding: the three strict Strong Hypotheses on Bound Constrained Exploratory Moves → StrictStrongMoves retains selected-column membership and feasibility and requires strict comparison with every feasible core value on the improving-core trigger; reason: For the finite feasible core this is the printed strict minimum rule; no arbitrary value is assigned to an empty minimum
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 9 (PDF p. 11), Proposition 4.3, both clauses

import Mathlib
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_StrictStrongMoves
open LewisTorczon.BoundPS

namespace BoundConstrainedPatternSearch.FullConvergence

/-- Proposition 4.3, printed p. 9 (PDF p. 11), both clauses. Column boundedness
and the strict strong moves are premises only of the second clause. All constants
are chosen before the iteration index. -/
theorem uniform_descent {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hcpt : IsCompact (levelSet lo hi f (R.x 0)))
    (hf : LevelSetRegularity lo hi f (R.x 0)) :
    (∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ k, R.Δ k < δ → η < ‖projQ lo hi f (R.x k)‖ →
        f (R.x k + R.s k) < f (R.x k) ∧ R.x k + R.s k ∈ box lo hi) ∧
    (BoundedCols R → StrictStrongMoves P lo hi f R →
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∃ σ : ℝ, 0 < σ ∧
        ∀ k, R.Δ k < δ → η < ‖projQ lo hi f (R.x k)‖ →
          f (R.x (k + 1)) ≤ f (R.x k) - σ * ‖projQ lo hi f (R.x k)‖ * ‖R.s k‖) := by sorry

end BoundConstrainedPatternSearch.FullConvergence
