-- Prove2me | Theorems.Thm_FatkhullinPolyak_Discrete_sublevel_bounded
-- name    : FatkhullinPolyak.Discrete.sublevel_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:37:35.872551+00:00
-- url     : https://prove2.me/theorems/23d2f6a0-a3d7-41ac-ae87-81989d9bf5c7
-- title:
--   Corollary 3.9 — the sublevel set $\mathcal S_0$ is bounded
-- statement:
--   Under the standing assumptions ($Q,R,\Sigma\succ0$, $\operatorname{rank}C=r$, $B\ne0$), for every stabilizing gain $K_0\in\mathcal S$ the sublevel set
--   $$\mathcal S_0=\{K\in\mathcal S: f(K)\le f(K_0)\}$$
--   is bounded: there is $M$ with $\|K\|_F\le M$ for all $K\in\mathcal S_0$.
--
--   Together with (3.1) this makes $\mathcal S_0$ a compact subset of the open set $\mathcal S$, the setting in which the gradient method is analysed.
-- source:
--   Fatkhullin, Polyak, Optimizing Static Linear Feedback: Gradient Method, arXiv:2004.09875v2, p. 7, Corollary 3.9

import Mathlib
import Definitions.Def_FatkhullinPolyak_Discrete_LQR

open Filter Topology

namespace FatkhullinPolyak.Discrete

/-- Corollary 3.9 (p. 7): for any `K₀ ∈ S` the sublevel set `S₀` is bounded. -/
theorem sublevel_bounded {n m r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin r) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (Sig : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q.PosDef) (hR : R.PosDef) (hSig : Sig.PosDef) (hC : C.rank = r) (hB : B ≠ 0)
    (K₀ : Matrix (Fin m) (Fin r) ℝ) (hK₀ : K₀ ∈ stabSet A B C) :
    ∃ M : ℝ, ∀ K ∈ sublevel A B C Q R Sig K₀, frobNorm K ≤ M := by sorry

end FatkhullinPolyak.Discrete
