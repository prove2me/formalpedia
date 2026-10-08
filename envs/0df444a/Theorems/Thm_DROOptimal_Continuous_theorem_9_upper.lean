-- Prove2me | Theorems.Thm_DROOptimal_Continuous_theorem_9_upper
-- name    : DROOptimal.Continuous.theorem_9_upper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:41.337624+00:00
-- url     : https://prove2.me/theorems/d707bfc3-22ba-4adc-b016-95b15fa758fc
-- title:
--   Theorem 9 (24a), p. 25 — limsup (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ −inf_{ℙ′ ∈ cl 𝒟} I(ℙ′,ℙ) for every 𝒟 ⊆ 𝒫
-- statement:
--   Let $\Xi\subseteq\mathbb R^d$ be compact, let $\mathcal P$ be the Borel probability distributions on $\Xi$ with the weak topology, and let $I$ be the relative entropy of Definition 8. Let $\xi_1,\xi_2,\dots$ be drawn independently from some $\mathbb P\in\mathcal P$, and let $\hat{\mathbb P}_T=\frac1T\sum_{t=1}^T\delta_{\xi_t}$.
--
--   **Theorem 9, upper bound (24a).** For every set $\mathcal D\subseteq\mathcal P$,
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)\le-\inf_{\mathbb P'\in\operatorname{cl}\mathcal D}I(\mathbb P',\mathbb P),
--   $$
--   where $\operatorname{cl}\mathcal D$ is the closure of $\mathcal D$ in the weak topology.
--
--   This is the large deviations upper bound of Sanov's theorem (the paper cites Csiszár 2006, §2). It is the probabilistic input of the feasibility half of Theorem 10. The closure cannot be dropped: that is the difference from the finite-state bound (7a).
--
--   **Formalization Note** The bound is stated without logarithms: for every finite $r'<\inf_{\operatorname{cl}\mathcal D}I(\cdot,\mathbb P)$, eventually $\mathbb P^\infty(\hat{\mathbb P}_T\in\mathcal D)\le e^{-r'T}$. An empty infimum is $+\infty$. The probability is the outer measure of the set of sample paths under the product measure.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 25, Theorem 9, (24a)

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Theorem 9, (24a) (p. 25): for i.i.d. samples from `ℙ ∈ 𝒫` and every `𝒟 ⊆ 𝒫`,
`limsup_T (1/T) log ℙ^∞(ℙ̂_T ∈ 𝒟) ≤ − inf_{ℙ′ ∈ cl 𝒟} I(ℙ′, ℙ)` (closure in the weak topology). -/
theorem theorem_9_upper {d : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} (hΞ : IsCompact Ξ)
    (ℙ : Dist Ξ) (D : Set (Dist Ξ)) :
    DecaysAtRate (⨅ ℙ' ∈ closure D, relEnt ℙ' ℙ) (fun T => sampleProb ℙ T (· ∈ D)) := by sorry

end DROOptimal.Continuous
