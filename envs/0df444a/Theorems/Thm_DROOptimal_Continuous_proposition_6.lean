-- Prove2me | Theorems.Thm_DROOptimal_Continuous_proposition_6
-- name    : DROOptimal.Continuous.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:30.701826+00:00
-- url     : https://prove2.me/theorems/56dc1b11-9800-4a17-97cc-3cb906e5a530
-- title:
--   Proposition 6, p. 25 — for r ≥ 0 the predictor ĉ_r is continuous on X × 𝒫
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence. Let $\hat c_r(x,\mathbb P')=\sup\{c(x,\mathbb P):\mathbb P\in\mathcal P,\ I(\mathbb P',\mathbb P)\le r\}$ with the relative entropy of Definition 8.
--
--   **Proposition 6 (Continuity of $\hat c_r$ revisited).** If $r\ge0$, then $\hat c_r$ is continuous on $X\times\mathcal P$, where $\mathcal P$ carries the weak topology.
--
--   Hence $\hat c_r$ belongs to the class $\mathcal C$ of data-driven predictors, which is the first half of its feasibility in (5) (Theorem 10).
--
--   **Formalization Note** The case $r=0$ is included as on the page: there $\hat c_0=c$ and the claim is Lemma 1.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 25, Proposition 6; proof p. 34

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Proposition 6 (p. 25): for `r ≥ 0`, `ĉ_r` is continuous on `X × 𝒫`. -/
theorem proposition_6 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r : ℝ) (hr : 0 ≤ r) :
    IsPredictor (drPredictor γ r) := by sorry

end DROOptimal.Continuous
