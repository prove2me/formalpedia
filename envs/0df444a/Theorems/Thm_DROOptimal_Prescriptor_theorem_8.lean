-- Prove2me | Theorems.Thm_DROOptimal_Prescriptor_theorem_8
-- name    : DROOptimal.Prescriptor.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:12:53.506+00:00
-- url     : https://prove2.me/theorems/257defcc-362b-4c68-a2d8-a7453f053750
-- title:
--   Theorem 8 (21), p. 22 — ℙ^∞(c(x̂_r(ℙ̂_T),ℙ) > ĉ_r(x̂_r(ℙ̂_T),ℙ̂_T)) ≤ (T+1)^d e^{−rT}
-- statement:
--   Assume the standing assumptions of §2: $X\subseteq\mathbb R^n$ is compact, $\Xi=\{1,\dots,d\}$ is finite, and the cost $\gamma(x,i)$ is continuous in $x$ for every $i\in\Xi$. Let $r\ge0$, let $\hat c_r$ be the distributionally robust predictor (10), and let $\hat x_r$ be a quasi-continuous selector of $\arg\min_{x\in X}\hat c_r(x,\cdot)$ (Definition 7). Then for every model $\mathbb P\in\mathcal P$ and every sample size $T\ge1$,
--   $$
--   \mathbb P^\infty\Big(c(\hat x_r(\hat{\mathbb P}_T),\mathbb P)>\hat c_r(\hat x_r(\hat{\mathbb P}_T),\hat{\mathbb P}_T)\Big)\le (T+1)^d e^{-rT}. \tag{21}
--   $$
--
--   This is the finite-sample counterpart of Theorem 6: the guarantee holds for each sample size, before any data are seen, and with an explicit polynomial prefactor.
--
--   **Formalization Note** The paper writes $\forall T\in\mathbb N$; the statement is posed for $T\ge1$, the sample sizes for which $\hat{\mathbb P}_T$ is defined. The paper takes $r\ge0$ in Definition 7, and so does the statement.
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 22, Theorem 8, (21)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

namespace DROOptimal.Prescriptor

/-- Theorem 8 (Finite sample guarantee), (21), p. 22: under the standing assumptions of §2 (p. 5), for
r ≥ 0, any quasi-continuous selector x̂_r of arg min_{x ∈ X} ĉ_r(x, ·), every model ℙ ∈ 𝒫 and every
sample size T ≥ 1,
ℙ^∞(c(x̂_r(ℙ̂_T), ℙ) > ĉ_r(x̂_r(ℙ̂_T), ℙ̂_T)) ≤ (T + 1)^d e^{−rT}. -/
theorem theorem_8 {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) (xr : DROOptimal.Predictor.Δ d → ↥X) (hxr_qc : QuasiContinuous xr)
    (hxr : IsArgminSelector (DROOptimal.Predictor.drPredictor γ r) xr) (ℙ : DROOptimal.Predictor.Δ d) (T : ℕ) (hT : 1 ≤ T) :
    DROOptimal.Predictor.empProb ℙ T (disappointSet γ (DROOptimal.Predictor.drPredictor γ r) xr ℙ)
      ≤ ((T : ℝ) + 1) ^ d * Real.exp (-(r * (T : ℝ))) := by sorry

end DROOptimal.Prescriptor
