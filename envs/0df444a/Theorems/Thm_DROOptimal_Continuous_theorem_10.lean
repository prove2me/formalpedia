-- Prove2me | Theorems.Thm_DROOptimal_Continuous_theorem_10
-- name    : DROOptimal.Continuous.theorem_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:04:38.818789+00:00
-- url     : https://prove2.me/theorems/aaacb3be-accb-4cac-b546-9f39e355a716
-- title:
--   Theorem 10, p. 26 — for r ≥ 0 the relative-entropy predictor ĉ_r is feasible in (5); for r > 0 it is strongly optimal in (5)
-- statement:
--   Throughout, $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ are compact, $\gamma:X\times\Xi\to\mathbb R$ is jointly continuous (the standing assumptions of §2, p. 5, and §5, p. 23), and $\mathcal P$ is the set of Borel probability distributions on $\Xi$ with the topology of weak convergence. Let $I$ be the relative entropy of Definition 8 and $\hat c_r(x,\mathbb P')=\sup\{c(x,\mathbb P):\mathbb P\in\mathcal P,\ I(\mathbb P',\mathbb P)\le r\}$ the distributionally robust predictor. Consider the meta-optimization problem (5): among predictors $\hat c$ that are continuous on $X\times\mathcal P$, minimize with respect to the pointwise order subject to
--   $$
--   \limsup_{T\to\infty}\frac1T\log\mathbb P^\infty\big(c(x,\mathbb P)>\hat c(x,\hat{\mathbb P}_T)\big)\le-r\qquad\forall x\in X,\ \mathbb P\in\mathcal P,
--   $$
--   where $\hat{\mathbb P}_T=\frac1T\sum_{t=1}^T\delta_{\xi_t}$ is the empirical distribution of $T$ independent samples from $\mathbb P$.
--
--   **Theorem 10 (Feasibility and optimality of $\hat c_r$ revisited).**
--
--   1. If $r\ge0$, then $\hat c_r$ is feasible in (5).
--   2. If $r>0$, then $\hat c_r$ is strongly optimal in (5): it is feasible, and $\hat c_r(x,\mathbb P')\le\hat c(x,\mathbb P')$ for all $x\in X$, $\mathbb P'\in\mathcal P$ and every feasible $\hat c$.
--
--   The theorem extends the main result of the paper (Theorem 4) from finite to compact continuous state spaces: the relative-entropy distributionally robust predictor is the least conservative continuous predictor whose out-of-sample disappointment decays at rate $r$.
--
--   **Formalization Note** Decay rates are encoded without logarithms (for every $r'<r$, eventually the disappointment is at most $e^{-r'T}$), so a disappointment that vanishes for large $T$ has rate $-\infty$. Predictors are required to be continuous for the weak topology on $\mathcal P$. The page's closing phrase "when $\epsilon>0$" in the proof is read as $r>0$, as in the statement.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 26, Theorem 10; proof pp. 35–36

import Mathlib
import Definitions.Def_DROOptimal_Continuous_Setting

namespace DROOptimal.Continuous

/-- Theorem 10 (p. 26): if `r ≥ 0`, the predictor `ĉ_r` is feasible in (5); if `r > 0`, it is strongly
optimal in (5). -/
theorem theorem_10 {d n : ℕ} {Ξ : Set (EuclideanSpace ℝ (Fin d))} {X : Set (EuclideanSpace ℝ (Fin n))}
    (hX : IsCompact X) (hΞ : IsCompact Ξ) (γ : ↥X → ↥Ξ → ℝ)
    (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2)) (r : ℝ) :
    (0 ≤ r → Feasible5 γ r (drPredictor γ r)) ∧
      (0 < r → StronglyOptimal5 γ r (drPredictor γ r)) := by sorry

end DROOptimal.Continuous
