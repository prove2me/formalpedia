-- Prove2me | Theorems.Thm_DROOptimal_Predictor_theorem_4
-- name    : DROOptimal.Predictor.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:47.008506+00:00
-- url     : https://prove2.me/theorems/ebd9790a-a0b9-4dc9-999f-80a09513efde
-- title:
--   Theorem 4, p. 17 — for r > 0 the relative-entropy DRO predictor ĉ_r is strongly optimal in (5)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, and $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$; write $c(x,\mathbb P)=\sum_i\mathbb P(i)\gamma(x,i)$ for the expected cost under a model $\mathbb P$ in the simplex $\mathcal P$, $I$ for the relative entropy, and $\hat{\mathbb P}_T$ for the empirical distribution of $T$ independent samples. For $r>0$ let
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}.
--   $$
--   Then $\hat c_r$ is strongly optimal in the vector optimization problem (5):
--
--   1. $\hat c_r$ is continuous on $X\times\mathcal P$, and for all $x\in X$ and $\mathbb P\in\mathcal P$,
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(c(x,\mathbb P)>\hat c_r(x,\hat{\mathbb P}_T)\big)\le-r ;
--   $$
--   2. every continuous $\hat c:X\times\mathcal P\to\mathbb R$ with the same property satisfies $\hat c_r(x,\mathbb P')\le\hat c(x,\mathbb P')$ for all $x\in X$ and $\mathbb P'\in\mathcal P$.
--
--   In words: among all data-driven predictors whose out-of-sample disappointment decays at exponential rate at least $r$ under every model, the relative-entropy distributionally robust predictor is the least conservative, uniformly in the decision and the observed frequencies.
--
--   **Formalization Note** The rate condition is the logarithm-free `RateLE` (equivalent to the displayed $\limsup$ with $\log0=-\infty$); the competitors range over all jointly continuous functions on $X\times\mathcal P$ and nothing else; feasibility of $\hat c_r$, continuity included, is part of the conclusion.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 17, Theorem 4; proof pp. 17–19

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5

namespace DROOptimal.Predictor

/-- Theorem 4 (Optimality of ĉ_r), p. 17: under the standing assumptions of §2 (p. 5), if r > 0
then ĉ_r is strongly optimal in (5): it is a continuous predictor whose disappointment decays at rate
at least r under every model and decision, and ĉ_r(x, ℙ′) ≤ ĉ(x, ℙ′) for all x ∈ X, ℙ′ ∈ 𝒫 and every
predictor ĉ feasible in (5). -/
theorem theorem_4 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) :
    StronglyOptimal5 γ r (drPredictor γ r) := by sorry

end DROOptimal.Predictor
