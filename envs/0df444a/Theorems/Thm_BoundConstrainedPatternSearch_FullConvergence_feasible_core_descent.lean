-- Prove2me | Theorems.Thm_BoundConstrainedPatternSearch_FullConvergence_feasible_core_descent
-- name    : BoundConstrainedPatternSearch.FullConvergence.feasible_core_descent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:40:38.605689+00:00
-- url     : https://prove2.me/theorems/821e7149-f86b-41ff-b879-92024e07376f
-- title:
--   Proposition 4.2 — feasible core descent with constant 1/√n
-- statement:
--   Let $\Omega=\{x\in\mathbb R^n:\ell\le x\le u\}$ with $\ell_j<u_j$ in every coordinate, allowing infinite bounds. Let $R=(x_k,\Delta_k,s_k,M_k,L_k)$ be a run of Algorithms 1–2, with fixed nonsingular basis $B$, finite nonsingular integer core family, diagonal $BM_k$, and the source's rational mesh updates. Write $P_\Omega$ for coordinatewise clamping, $g=\nabla f$ for the actual ambient gradient of $f:\mathbb R^n\to\mathbb R$, $q(x)=P_\Omega(x-g(x))-x$, and $S=L_\Omega(x_0)$. Assume ambient differentiability at every point of $S$ and continuity of $g$ restricted to $S$.
--
--   Fix an iteration $k$ with $q(x_k)\ne0$. There is $\nu_k>0$, chosen for this point and core before the test mesh, such that every $0<\Delta<\nu_k$ admits a core column $c\in\Gamma_k$ whose step $s=\Delta Bc$ satisfies
--
--   $$
--   x_k+s\in\Omega,\qquad
--   \langle g(x_k),s\rangle\le-\frac1{\sqrt n}\,\|q(x_k)\|\,\|s\|.
--   $$
--
--   This is the source's feasible descent-direction result at its exact dimension constant. Compactness, bounded generating columns and strong exploratory moves are unnecessary here. The premise $q(x_k)\ne0$ itself excludes dimension zero.
--
--   Differences from the source:
--   - encoding: real Euclidean vectors with coordinates 1 through n and possibly infinite box bounds → EuclideanSpace ℝ (Fin n), zero-based coordinates, EReal endpoints with lo j < hi j; reason: Reindexing preserves every finite dimension; strict gaps make the clamped value finite even for missing bounds
--   - encoding: Algorithms 1–2 and the finite feasible-core minimum rule → published GPSParams, GPSRun and IsGPSRun with actual column membership and an existential improving-core trigger; reason: The finite minimum improves exactly when a feasible core column improves; the empty-core trigger is false, and all rational updates, zero columns and diagonal cores are retained
--   - reading: f continuously differentiable on the closed feasible level set L_Ω(x₀) → ambient differentiability at every point of L_Ω(x₀) and continuity of the actual ambient gradient restricted to that set; reason: This specifies closed-set regularity even with empty interior, includes neighborhood-C¹ instances and requires no regularity elsewhere in Ω
--   - reading: there exists ν_k > 0 such that if Δ_k < ν_k a feasible core descent step exists → at fixed x_k and core, ν is chosen before every positive test mesh Δ < ν; reason: The construction ν_k = ‖q_k‖∞ / |d_k^m| on printed pp. 8–9 is independent of the test mesh; this makes the intended threshold assertion nonvacuous
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 8 (PDF p. 10), Proposition 4.2

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_GPS
import Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_LevelSetRegularity
open LewisTorczon.BoundPS

namespace BoundConstrainedPatternSearch.FullConvergence

/-- Proposition 4.2, printed p. 8 (PDF p. 10). The threshold precedes every
positive test mesh at this fixed point and core. Nonzero q excludes dimension zero. -/
theorem feasible_core_descent {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (hlohi : ∀ j, lo j < hi j) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (R : GPSRun n m) (hR : IsGPSRun P lo hi f R)
    (hf : LevelSetRegularity lo hi f (R.x 0)) (k : ℕ)
    (hq : projQ lo hi f (R.x k) ≠ 0) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ Δ : ℝ, 0 < Δ → Δ < ν →
      ∃ c ∈ coreCols R k, R.x k + stepOf P Δ c ∈ box lo hi ∧
        inner ℝ (gradient f (R.x k)) (stepOf P Δ c) ≤
          -(1 / Real.sqrt n) * ‖projQ lo hi f (R.x k)‖ * ‖stepOf P Δ c‖ := by sorry

end BoundConstrainedPatternSearch.FullConvergence
