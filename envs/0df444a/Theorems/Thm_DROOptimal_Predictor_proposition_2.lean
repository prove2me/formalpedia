-- Prove2me | Theorems.Thm_DROOptimal_Predictor_proposition_2
-- name    : DROOptimal.Predictor.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:54.344975+00:00
-- url     : https://prove2.me/theorems/1a563842-a524-4de4-8c21-bd4b9b141722
-- title:
--   Proposition 2, (11), p. 15 — ĉ_r(x,ℙ′) = min_{α≥γ̄(x)} α − e^{−r} Π_i (α−γ(x,i))^{ℙ′(i)}, with a bracketed minimizer
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$, $c(x,\mathbb P)=\sum_i\mathbb P(i)\gamma(x,i)$, and let $\hat c_r$ be the distributionally robust predictor (10). If $r>0$ and $\bar\gamma(x)=\max_{i\in\Xi}\gamma(x,i)$ is the worst-case cost, then for every $x\in X$ and $\mathbb P'\in\mathcal P$,
--   $$
--   \hat c_r(x,\mathbb P')=\min_{\alpha\ge\bar\gamma(x)}\ \alpha-e^{-r}\prod_{i\in\Xi}\big(\alpha-\gamma(x,i)\big)^{\mathbb P'(i)} ,
--   $$
--   and this minimum is attained at some $\alpha^\star$ with
--   $$
--   \bar\gamma(x)\le\alpha^\star\le\frac{\bar\gamma(x)-e^{-r}c(x,\mathbb P')}{1-e^{-r}} .
--   $$
--
--   The dual representation reduces the evaluation of $\hat c_r$ to a one-dimensional convex problem and is the basis of the continuity of $\hat c_r$ (Proposition 3).
--
--   **Formalization Note** "min" is stated as: $\hat c_r(x,\mathbb P')$ is a value of the objective at some $\alpha\ge\bar\gamma(x)$ and is below all such values. Powers are real powers with $0^0=1$, so outcomes with $\mathbb P'(i)=0$ contribute a factor $1$. $\bar\gamma(x)$ is written as $\sup_i\gamma(x,i)$, which is the maximum because $\Xi$ is finite and nonempty whenever $\mathcal P$ is.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 15, Proposition 2, (11); proof in Appendix A, p. 28

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- Proposition 2 (Dual representation of ĉ_r), (11), p. 15: if r > 0 and
γ̄(x) = max_{i ∈ Ξ} γ(x, i), then
ĉ_r(x, ℙ′) = min_{α ≥ γ̄(x)} α − e^{−r} Π_{i ∈ Ξ} (α − γ(x, i))^{ℙ′(i)},
and problem (11) has a minimizer α⋆ with γ̄(x) ≤ α⋆ ≤ (γ̄(x) − e^{−r} c(x, ℙ′)) / (1 − e^{−r}).
Powers are `Real.rpow` (0^0 = 1). -/
theorem proposition_2 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) (x : ↥X) (ℙ' : Δ d) :
    IsLeast {v : ℝ | ∃ α : ℝ, (⨆ i, γ x i) ≤ α ∧
        v = α - Real.exp (-r) * ∏ i, (α - γ x i) ^ ((ℙ' : Fin d → ℝ) i)}
      (drPredictor γ r x ℙ') ∧
    ∃ αstar : ℝ, (⨆ i, γ x i) ≤ αstar ∧
      αstar ≤ ((⨆ i, γ x i) - Real.exp (-r) * cost γ x ℙ') / (1 - Real.exp (-r)) ∧
      drPredictor γ r x ℙ' =
        αstar - Real.exp (-r) * ∏ i, (αstar - γ x i) ^ ((ℙ' : Fin d → ℝ) i) := by sorry

end DROOptimal.Predictor
