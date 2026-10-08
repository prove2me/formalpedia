-- Prove2me | Theorems.Thm_DROOptimal_Continuous_lemma_1
-- name    : DROOptimal.Continuous.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:30.437197+00:00
-- url     : https://prove2.me/theorems/a41dc9cc-78f2-4487-ac69-e86916f66c30
-- title:
--   Lemma 1, p. 23 — if γ is continuous on compact X × Ξ, then c(x,ℙ) is continuous on X × 𝒫
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence.
--
--   **Lemma 1 (Continuity of model-based predictors).** The model-based predictor
--   $$
--   c(x,\mathbb P)=\int_\Xi\gamma(x,\xi)\,\mathrm d\mathbb P(\xi)
--   $$
--   is continuous on $X\times\mathcal P$, where $X$ carries the Euclidean topology and $\mathcal P$ the weak topology.
--
--   Thus $c$ belongs to the class $\mathcal C$ of data-driven predictors, and model-based prescriptors $x^\star(\mathbb P)\in\arg\min_{x\in X}c(x,\mathbb P)$ exist. The lemma is used in the continuity proof for $\hat c_r$ (Proposition 6).
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 23, Lemma 1; proof p. 29

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Lemma 1 (p. 23): if `γ` is continuous on the compact set `X × Ξ`, then `c(x, ℙ)` is continuous
on `X × 𝒫` (weak topology on 𝒫). -/
theorem lemma_1 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) :
    IsPredictor (cost γ) := by sorry

end DROOptimal.Continuous
