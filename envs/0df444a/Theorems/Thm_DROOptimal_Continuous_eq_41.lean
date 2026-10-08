-- Prove2me | Theorems.Thm_DROOptimal_Continuous_eq_41
-- name    : DROOptimal.Continuous.eq_41
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:36.849413+00:00
-- url     : https://prove2.me/theorems/f4a3fb9a-2a88-4208-a02d-9f7297d1c21c
-- title:
--   (41), proof of Theorem 10, Case 2, p. 35 — if ℙ₀(Ξ⋆(x)) < 1, then c(x,ℙ₀) ≥ ĉ_r(x,ℙ′) implies I(ℙ′,ℙ₀) ≥ r
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence. Let $I$ be the relative entropy of Definition 8, $\hat c_r$ the distributionally robust predictor, and $\Xi^\star(x)=\arg\max_{\xi\in\Xi}\gamma(x,\xi)$ the set of worst-case scenarios.
--
--   **Implication (41).** Let $r\ge0$, $x\in X$ and $\mathbb P_0\in\mathcal P$ with $\mathbb P_0(\Xi^\star(x))<1$. Define the weak disappointment set $\bar{\mathcal D}(x,\mathbb P_0)=\{\mathbb P'\in\mathcal P: c(x,\mathbb P_0)\ge\hat c_r(x,\mathbb P')\}$. Then
--   $$
--   \mathbb P'\in\bar{\mathcal D}(x,\mathbb P_0)\quad\Longrightarrow\quad I(\mathbb P',\mathbb P_0)\ge r .
--   $$
--
--   Combined with the closedness of $\bar{\mathcal D}(x,\mathbb P_0)$ (from Proposition 6) and the upper bound (24a), this gives the decay rate $r$ of the disappointment in the feasibility half of Theorem 10. The hypothesis $\mathbb P_0(\Xi^\star(x))<1$ cannot be dropped: when $\mathbb P_0$ is concentrated on the worst-case scenarios, $\mathbb P_0$ itself lies in $\bar{\mathcal D}(x,\mathbb P_0)$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 35, proof of Theorem 10, Case 2, (41); proof pp. 35–36

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Implication (41) (proof of Theorem 10, Case 2, p. 35): if `ℙ₀(Ξ⋆(x)) < 1`, then every `ℙ′` in the
weak disappointment set `𝒟̄(x, ℙ₀) = {ℙ′ : c(x, ℙ₀) ≥ ĉ_r(x, ℙ′)}` has `I(ℙ′, ℙ₀) ≥ r`. -/
theorem eq_41 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r : ℝ) (hr : 0 ≤ r) (x : ↥X) (ℙ₀ : Dist Ξ)
    (hcase2 : (ℙ₀ : MeasureTheory.Measure ↥Ξ) (worstSet γ x) < 1) (ℙ' : Dist Ξ)
    (hD : drPredictor γ r x ℙ' ≤ cost γ x ℙ₀) :
    ENNReal.ofReal r ≤ relEnt ℙ' ℙ₀ := by sorry

end DROOptimal.Continuous
