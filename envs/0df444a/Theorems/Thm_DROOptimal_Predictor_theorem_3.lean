-- Prove2me | Theorems.Thm_DROOptimal_Predictor_theorem_3
-- name    : DROOptimal.Predictor.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:10:43.851406+00:00
-- url     : https://prove2.me/theorems/a3182e28-ae93-4179-b52e-e3ec0336aa80
-- title:
--   Theorem 3, p. 16 — for r ≥ 0 the predictor ĉ_r is feasible in (5)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be compact, $\Xi=\{1,\dots,d\}$, $\gamma:X\times\Xi\to\mathbb R$ continuous in $x$ for each $i$, and $\hat c_r$ the distributionally robust predictor (10). If $r\ge0$, then $\hat c_r$ is continuous on $X\times\mathcal P$ and
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(c(x,\mathbb P)>\hat c_r(x,\hat{\mathbb P}_T)\big)\le-r\qquad\forall x\in X,\ \mathbb P\in\mathcal P ,
--   $$
--   where $\hat{\mathbb P}_T$ is the empirical distribution of $T$ independent samples from $\mathbb P$; i.e. $\hat c_r$ is feasible in (5).
--
--   This is the first half of the main result (Theorem 4): the out-of-sample disappointment of $\hat c_r$ decays at rate at least $r$ under every model.
--
--   **Formalization Note** The rate condition is the logarithm-free `RateLE` of the `Setting` module (for every $r'<r$, eventually the disappointment is at most $e^{-r'T}$), equivalent to the displayed $\limsup$ with $\log0=-\infty$.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 16, Theorem 3; proof pp. 16–17

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Predictor_Problem5

namespace DROOptimal.Predictor

/-- Theorem 3 (Feasibility of ĉ_r), p. 16: under the standing assumptions of §2 (p. 5), if r ≥ 0
then the predictor ĉ_r is feasible in (5). -/
theorem theorem_3 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) :
    Feasible5 γ r (drPredictor γ r) := by sorry

end DROOptimal.Predictor
