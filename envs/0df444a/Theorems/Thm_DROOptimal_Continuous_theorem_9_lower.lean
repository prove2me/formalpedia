-- Prove2me | Theorems.Thm_DROOptimal_Continuous_theorem_9_lower
-- name    : DROOptimal.Continuous.theorem_9_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:35.168743+00:00
-- url     : https://prove2.me/theorems/9009190b-a890-4256-8773-b1da12f4196f
-- title:
--   Theorem 9 (24b), p. 25 — liminf (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≥ −inf_{ℙ′ ∈ int 𝒟} I(ℙ′,ℙ) for every 𝒟 ⊆ 𝒫
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be compact, let $\mathcal P$ be the Borel probability distributions on $\Xi$ with the weak topology, and let $I$ be the relative entropy of Definition 8. Let $\xi_1,\xi_2,\dots$ be drawn independently from some $\mathbb P\in\mathcal P$, and let $\hat{\mathbb P}_T=\frac1T\sum_{t=1}^T\delta_{\xi_t}$.
--
--   **Theorem 9, lower bound (24b).** For every set $\mathcal D\subseteq\mathcal P$,
--   $$
--   \liminf_{T\to\infty}\frac1T\log\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)\ge-\inf_{\mathbb P'\in\operatorname{int}\mathcal D}I(\mathbb P',\mathbb P),
--   $$
--   where $\operatorname{int}\mathcal D$ is the interior of $\mathcal D$ in the weak topology. No positivity assumption on $\mathbb P$ is made.
--
--   This is the large deviations lower bound of Sanov's theorem (the paper cites Csiszár 2006, §2). It is used when the proof of Theorem 4 is repeated to show strong optimality of $\hat c_r$ (Theorem 10).
--
--   **Formalization Note** The bound is stated without logarithms: for every finite $s'>\inf_{\operatorname{int}\mathcal D}I(\cdot,\mathbb P)$, eventually $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)\ge e^{-s'T}$; the statement is vacuous when the infimum is $+\infty$. The probability is the outer measure of the set of sample paths under the product measure.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 25, Theorem 9, (24b)

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Theorem 9, (24b) (p. 25): for i.i.d. samples from `ℙ ∈ 𝒫` and every `𝒟 ⊆ 𝒫`,
`liminf_T (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≥ − inf_{ℙ′ ∈ int 𝒟} I(ℙ′, ℙ)` (interior in the weak topology). -/
theorem theorem_9_lower {d : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} (hΞ : IsCompact Ξ)
    (ℙ : Dist Ξ) (D : Set (Dist Ξ)) :
    DecaysAtMostAtRate (⨅ ℙ' ∈ interior D, relEnt ℙ' ℙ)
      (fun T => sampleProb ℙ T (· ∈ D)) := by sorry

end DROOptimal.Continuous
