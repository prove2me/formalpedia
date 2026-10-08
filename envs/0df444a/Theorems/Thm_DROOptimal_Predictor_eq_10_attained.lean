-- Prove2me | Theorems.Thm_DROOptimal_Predictor_eq_10_attained
-- name    : DROOptimal.Predictor.eq_10_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:09:55.724293+00:00
-- url     : https://prove2.me/theorems/b4ba6657-c206-4fa7-8b0c-fc49c34c14e1
-- title:
--   §4.1, p. 14 — for r ≥ 0 the supremum in (10) defining ĉ_r(x,ℙ′) is attained
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$, $c(x,\mathbb P)=\sum_i\mathbb P(i)\gamma(x,i)$, and
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}
--   $$
--   the distributionally robust predictor (10). If $r\ge0$, then for every $x\in X$ and $\mathbb P'\in\mathcal P$ there is $\mathbb P_0\in\mathcal P$ with
--   $$
--   I(\mathbb P',\mathbb P_0)\le r\qquad\text{and}\qquad \hat c_r(x,\mathbb P')=c(x,\mathbb P_0).
--   $$
--
--   The proof of Theorem 4 starts from such a maximizer $\mathbb P_0$ (display (14)).
--
--   **Formalization Note** The supremum is a real `sSup`; the statement asserts that it equals a value of $c(x,\cdot)$ at a feasible model, i.e. that it is a maximum. The standing assumptions of §2 (compact $X$, continuous $\gamma$) are carried although only the fixed decision $x$ matters here.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 14, §4.1, after Definition 6 (unnumbered claim on (10))

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting

namespace DROOptimal.Predictor

/-- §4.1, p. 14, after Definition 6: for r ≥ 0 the supremum in (10) is attained, i.e. for every
x ∈ X and ℙ′ ∈ 𝒫 there is ℙ₀ ∈ 𝒫 with I(ℙ′, ℙ₀) ≤ r and ĉ_r(x, ℙ′) = c(x, ℙ₀). -/
theorem eq_10_attained {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) (x : ↥X) (ℙ' : Δ d) :
    ∃ ℙ₀ : Δ d, relEntropy ℙ' ℙ₀ ≤ (r : EReal) ∧ drPredictor γ r x ℙ' = cost γ x ℙ₀ := by sorry

end DROOptimal.Predictor
