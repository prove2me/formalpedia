-- Prove2me | Theorems.Thm_DROOptimal_Predictor_Supplement_theorem_5
-- name    : DROOptimal.Predictor.Supplement.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:46:46.569154+00:00
-- url     : https://prove2.me/theorems/624376c4-73a5-4dc9-bbef-6d2cda5a4624
-- title:
--   Theorem 5 (Finite sample guarantee), (17), p. 19 — ℙ^∞(c(x,ℙ) > ĉ_r(x,ℙ̂_T)) ≤ (T+1)^d e^{−rT}
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$, $r\ge0$, and $\hat c_r$ the distributionally robust predictor (10). For every model $\mathbb P\in\mathcal P$, every $x\in X$ and every $T\ge1$,
--   $$
--   \mathbb P^\infty\big(c(x,\mathbb P)>\hat c_r(x,\hat{\mathbb P}_T)\big)\le(T+1)^d\,e^{-rT},
--   $$
--   where $\hat{\mathbb P}_T$ is the empirical distribution of $T$ independent samples from $\mathbb P$.
--
--   This is the finite-sample counterpart of the feasibility of $\hat c_r$ (Theorem 3).
--
--   **Formalization Note** $r\ge0$ is the range of Definition 6 and is assumed. The paper writes $\forall T\in\mathbb N$; the empirical distribution is defined for $T\ge1$ only, so $T\ge1$ is assumed.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 19, Theorem 5, (17)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5

namespace DROOptimal.Predictor.Supplement

/-- Theorem 5 (Finite sample guarantee), (17), p. 19: under the standing assumptions of §2 (p. 5),
for r ≥ 0 (Definition 6), every model ℙ ∈ 𝒫, every x ∈ X and every T ≥ 1,
ℙ^∞(c(x, ℙ) > ĉ_r(x, ℙ̂_T)) ≤ (T + 1)^d e^{−rT}. -/
theorem theorem_5 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) (x : ↥X) (ℙ : Δ d) (T : ℕ) (hT : 1 ≤ T) :
    empProb ℙ T (disappointSet γ (drPredictor γ r) x ℙ) ≤
      ((T : ℝ) + 1) ^ d * Real.exp (-(r * (T : ℝ))) := by sorry

end DROOptimal.Predictor.Supplement
