-- Prove2me | Theorems.Thm_DROOptimal_Prescriptor_theorem_6
-- name    : DROOptimal.Prescriptor.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:53.802182+00:00
-- url     : https://prove2.me/theorems/1e792614-2823-447b-8e22-29ad666a4223
-- title:
--   Theorem 6, p. 20 — for r ≥ 0 the pair (ĉ_r, x̂_r) is feasible in (6)
-- statement:
--   Assume the standing assumptions of §2: $X\subseteq\mathbb R^n$ is compact, $\Xi=\{1,\dots,d\}$ is finite, and the cost $\gamma(x,i)$ is continuous in $x$ for every $i\in\Xi$. Let $r\ge0$, let $\hat c_r$ be the distributionally robust predictor (10), and let $\hat x_r:\mathcal P\to X$ be any quasi-continuous function with $\hat x_r(\mathbb P')\in\arg\min_{x\in X}\hat c_r(x,\mathbb P')$ for all $\mathbb P'\in\mathcal P$ (Definition 7). Then the pair $(\hat c_r,\hat x_r)$ is feasible in problem (6): it belongs to the family $\mathcal X$ (in particular $\hat c_r$ is continuous on $X\times\mathcal P$), and for every model $\mathbb P\in\mathcal P$
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\Big(c(\hat x_r(\hat{\mathbb P}_T),\mathbb P)>\hat c_r(\hat x_r(\hat{\mathbb P}_T),\hat{\mathbb P}_T)\Big)\le -r .
--   $$
--
--   The prescriptions of the distributionally robust pair therefore disappoint with a probability that decays exponentially at rate at least $r$, whatever the data-generating model.
--
--   **Formalization Note** The rate is stated without logarithms: for every $r'<r$, the probability is eventually at most $e^{-r'T}$. Continuity of $\hat c_r$ (Proposition 3 of the paper) is part of the conclusion, not a hypothesis.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 20, Theorem 6

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

namespace DROOptimal.Prescriptor

/-- Theorem 6 (Feasibility of (ĉ_r, x̂_r)), p. 20: under the standing assumptions of §2 (p. 5), if
r ≥ 0 and x̂_r is any quasi-continuous selector of arg min_{x ∈ X} ĉ_r(x, ·) (Definition 7, (18)), then
the pair (ĉ_r, x̂_r) is feasible in (6). -/
theorem theorem_6 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) (xr : DROOptimal.Predictor.Δ d → ↥X) (hxr_qc : QuasiContinuous xr)
    (hxr : IsArgminSelector (DROOptimal.Predictor.drPredictor γ r) xr) :
    Feasible6 γ r (DROOptimal.Predictor.drPredictor γ r) xr := by sorry

end DROOptimal.Prescriptor
