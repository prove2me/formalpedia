-- Prove2me | Theorems.Thm_DROOptimal_Prescriptor_theorem_7
-- name    : DROOptimal.Prescriptor.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:13:28.120979+00:00
-- url     : https://prove2.me/theorems/dd8c12c2-e724-493e-a051-937517ad0aed
-- title:
--   Theorem 7, p. 20 — for r > 0 the relative-entropy robust pair (ĉ_r, x̂_r) is strongly optimal in (6)
-- statement:
--   Assume the standing assumptions of §2: $X\subseteq\mathbb R^n$ is compact, $\Xi=\{1,\dots,d\}$ is finite, and the cost $\gamma(x,i)$ is continuous in $x$ for every $i\in\Xi$. Let $r>0$, let
--   $$
--   \hat c_r(x,\mathbb P')=\sup_{\mathbb P\in\mathcal P}\{c(x,\mathbb P): I(\mathbb P',\mathbb P)\le r\}
--   $$
--   be the distributionally robust predictor, and let $\hat x_r:\mathcal P\to X$ be any quasi-continuous function with $\hat x_r(\mathbb P')\in\arg\min_{x\in X}\hat c_r(x,\mathbb P')$ for all $\mathbb P'$ (Definition 7). Then $(\hat c_r,\hat x_r)$ is strongly optimal in problem (6):
--
--   1. $(\hat c_r,\hat x_r)$ is feasible in (6): it belongs to the family $\mathcal X$ of data-driven predictor–prescriptor pairs and its prescription disappointment decays at rate at least $r$ under every model $\mathbb P\in\mathcal P$;
--   2. for every pair $(\hat c,\hat x)\in\mathcal X$ that is feasible in (6),
--   $$
--   \hat c_r(\hat x_r(\mathbb P'),\mathbb P')\le\hat c(\hat x(\mathbb P'),\mathbb P')\qquad\forall\,\mathbb P'\in\mathcal P .
--   $$
--
--   In words, no data-driven predictor–prescriptor pair whose prescriptions disappoint with probability decaying at rate $r$ can report a smaller in-sample optimal value than the distributionally robust pair, at any realization of the empirical distribution. Distributionally robust optimization with a relative-entropy ball of radius $r$ is thus the least conservative way to obtain this out-of-sample guarantee.
--
--   **Formalization Note** The statement quantifies over every quasi-continuous selector $\hat x_r$, as the theorem does; Proposition 4 shows one exists. Competing pairs range over continuous predictors with quasi-continuous arg-min selectors; the order compares in-sample optimal values $\hat c(\hat x(\mathbb P'),\mathbb P')$, not the predictors pointwise. The rate is stated without logarithms (for every $r'<r$, eventually at most $e^{-r'T}$), and the relative entropy takes the value $+\infty$ when $\mathbb P(i)=0<\mathbb P'(i)$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 20, Theorem 7; proof pp. 20–21

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

namespace DROOptimal.Prescriptor

/-- Theorem 7 (Optimality of (ĉ_r, x̂_r)), p. 20: under the standing assumptions of §2 (p. 5), if
r > 0 and x̂_r is any quasi-continuous selector of arg min_{x ∈ X} ĉ_r(x, ·) (Definition 7, (18)), then
(ĉ_r, x̂_r) is strongly optimal in (6): it is feasible in (6), and every pair (ĉ, x̂) ∈ 𝒳 feasible in (6)
satisfies ĉ_r(x̂_r(ℙ′), ℙ′) ≤ ĉ(x̂(ℙ′), ℙ′) for all ℙ′ ∈ 𝒫. -/
theorem theorem_7 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) (xr : DROOptimal.Predictor.Δ d → ↥X) (hxr_qc : QuasiContinuous xr)
    (hxr : IsArgminSelector (DROOptimal.Predictor.drPredictor γ r) xr) :
    StronglyOptimal6 γ r (DROOptimal.Predictor.drPredictor γ r) xr := by sorry

end DROOptimal.Prescriptor
