-- Prove2me | Theorems.Thm_DROOptimal_Predictor_eq_15
-- name    : DROOptimal.Predictor.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:06.228461+00:00
-- url     : https://prove2.me/theorems/4dcf687d-4062-4bb5-ae56-ec71b97362e8
-- title:
--   (15), proof of Theorem 4, p. 18 — a strictly positive ℙ₂ with I(ℙ′₀,ℙ₂) < r and c(x,ℙ₀) < c(x,ℙ₂) + ϵ
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$, $c(x,\mathbb P)=\sum_i\mathbb P(i)\gamma(x,i)$, and $I$ the relative entropy. Let $r>0$, $x\in X$, and let $\mathbb P_0',\mathbb P_0\in\mathcal P$ satisfy $I(\mathbb P_0',\mathbb P_0)\le r$ and $\hat c_r(x,\mathbb P_0')=c(x,\mathbb P_0)$. Then for every $\epsilon>0$ there is $\mathbb P_2\in\mathcal P$ with
--   $$
--   \mathbb P_2(i)>0\ \ \forall i\in\Xi,\qquad I(\mathbb P_0',\mathbb P_2)<r,\qquad c(x,\mathbb P_0)<c(x,\mathbb P_2)+\epsilon .
--   $$
--
--   In the proof of Theorem 4, $\mathbb P_0$ is a maximizer in (10); the model $\mathbb P_2$ is almost as costly as $\mathbb P_0$, strictly inside the relative entropy ball, and strictly positive, so that the large deviation lower bound (7b) applies to it.
--
--   **Formalization Note** The paper also records $0<r_2=I(\mathbb P_0',\mathbb P_2)$. That clause is dropped: it is never used, and it can fail (for $d=1$ the relative entropy vanishes identically). The decision $x$ is fixed; $\mathbb P_2$ may depend on it.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 18, display (15) in the proof of Theorem 4 (with (14), p. 17)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Display (15), proof of Theorem 4, pp. 17–18: let r > 0, x ∈ X, ℙ′₀ ∈ 𝒫 and let ℙ₀ ∈ 𝒫 satisfy
I(ℙ′₀, ℙ₀) ≤ r and ĉ_r(x, ℙ′₀) = c(x, ℙ₀) (as in (14)). Then for every ϵ > 0 there is ℙ₂ ∈ 𝒫 with ℙ₂ > 0,
I(ℙ′₀, ℙ₂) < r and c(x, ℙ₀) < c(x, ℙ₂) + ϵ. -/
theorem eq_15 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) (x : ↥X) (ℙ'₀ ℙ₀ : Δ d) (h14 : relEntropy ℙ'₀ ℙ₀ ≤ (r : EReal))
    (hOpt : drPredictor γ r x ℙ'₀ = cost γ x ℙ₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ ℙ₂ : Δ d, (∀ i, 0 < (ℙ₂ : Fin d → ℝ) i) ∧ relEntropy ℙ'₀ ℙ₂ < (r : EReal) ∧
      cost γ x ℙ₀ < cost γ x ℙ₂ + ε := by sorry

end DROOptimal.Predictor
