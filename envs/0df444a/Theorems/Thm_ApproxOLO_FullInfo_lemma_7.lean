-- Prove2me | Theorems.Thm_ApproxOLO_FullInfo_lemma_7
-- name    : ApproxOLO.FullInfo.lemma_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:52.437654+00:00
-- url     : https://prove2.me/theorems/b6b6f9a1-2914-4c60-8ceb-0af40632593e
-- title:
--   Lemma 7, p. 12 — Algorithm 2 terminates with an infeasible projection ỹ onto CH(αK) that is 3ε-close to a convex combination of oracle outputs
-- statement:
--   There is a universal constant $c>0$ (the constant of Lemma 5 that sets the number of Ellipsoid iterations in each call) such that the following holds. Let $d\ge2$, let $\mathcal K,\mathcal F,R,F,C$ be an instance, $\mathcal O_{\mathcal K}$ an $\alpha$-approximation oracle ($\alpha>0$), $y\in\mathbb R^d$ and $\varepsilon\in(0,(\alpha+2)R]$. Then Algorithm 2 on input $(y,\varepsilon)$ terminates, and every terminating run returns a point $\tilde y\in\mathbb R^d$, a distribution $(a_1,\dots,a_N)$ and extended-oracle outputs $\{(v_1,s_1),\dots,(v_N,s_N)\}$, with $N$ as prescribed in Lemma 5, such that
--
--   1. $$\forall z\in\mathrm{CH}(\alpha\mathcal K):\quad\|\tilde y-z\|^2\le\|y-z\|^2;$$
--   2. $$\|p-\tilde y\|\le3\varepsilon\quad\text{for }p:=\sum_{i=1}^Na_iv_i.$$
--
--   So $\tilde y$ is an infeasible projection of $y$ onto $\mathrm{CH}(\alpha\mathcal K)$ in the sense of Eq. (3), and it lies within $3\varepsilon$ of an explicit convex combination of oracle outputs; this is the projection step of Algorithm 3.
--
--   **Formalization Note** The page also states that Algorithm 2 terminates after at most $\lceil\alpha^2R^2/\varepsilon^2\rceil$ iterations. That count does not follow from the proof (which gives $1+\mathrm{dist}^2(\tilde y_1,\mathrm{CH}(\alpha\mathcal K))/\varepsilon^2$, up to $1+4\alpha^2R^2/\varepsilon^2$) and a hand trace in dimension one (where the ellipsoid method is bisection) enters the loop more often than it allows, so the printed iteration bound is replaced by termination (existence of a complete run); see the moderation notes. The "Moreover" clause of the page (distance and query-count bounds) is not part of this statement. Each call of the procedure of Lemma 5 may use its own iteration budget $N$, a positive integer at least $c\,d^2\ln(((\alpha+1)R+\|\tilde y\|)/\varepsilon)$ for the current $\tilde y$. The Ellipsoid method is the one fixed in the model (start $\mathcal B(0,1)$, central cuts); $d\ge2$ as in Lemma 5. $\|\cdot\|$ is Euclidean.
-- source:
--   Garber, Efficient Online Linear Optimization with Approximation Algorithms, arXiv:1709.03093v1, p. 12, Lemma 7 (Algorithm 2)

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model

namespace ApproxOLO.FullInfo

open Matrix

/-- **Lemma 7, Garber, arXiv:1709.03093v1, p. 12 (items 1–2, with termination).** There is a
universal constant `c > 0` (the constant of Lemma 5 that fixes the number of Ellipsoid
iterations per call) such that for every `d ≥ 2`, instance, `α > 0`, oracle, `y ∈ ℝ^d` and
`ε ∈ (0, (α + 2)R]`: Algorithm 2 on `(y, ε)` has a complete (terminating) run, and every
complete run returns `ỹ`, `(a_1, …, a_N)` and oracle outputs `{(v_i, s_i)}` with
1. `‖ỹ − z‖² ≤ ‖y − z‖²` for all `z ∈ CH(αK)`;
2. `‖p − ỹ‖ ≤ 3ε` for `p = Σ_i a_i v_i`. -/
theorem lemma_7 : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
    ∀ (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d) (y : Vec d) (eps : ℝ),
    IsInstance K Fs R Fb C → 0 < alpha → IsApproxOracle K alpha O →
    0 < eps → eps ≤ (alpha + 2) * R →
    (∃ out : Alg2Out d, IsAlg2Run c O alpha R y eps out) ∧
    ∀ out : Alg2Out d, IsAlg2Run c O alpha R y eps out →
      (∀ z ∈ scaledHull K alpha, euclNorm (out.yt - z) ^ 2 ≤ euclNorm (y - z) ^ 2) ∧
      euclNorm (∑ i, out.a i • (out.pts i).1 - out.yt) ≤ 3 * eps := by sorry

end ApproxOLO.FullInfo
