-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_prop2_pointwise_convergence
-- name    : BHTOpinion.Continuum.prop2_pointwise_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:11.951192+00:00
-- url     : https://prove2.me/theorems/55098df2-146e-49a9-bc5d-c109788c26c3
-- title:
--   Proposition 2 — x_t(α) converges for every α ∈ I outside a countable set
-- statement:
--   Let $x$ be a solution of the integral equation (3.2) such that $x_t$ is nondecreasing in $\alpha$ for every $t\ge0$. Then there is a countable set $S\subseteq\mathbb R$ such that for every agent $\alpha\in I\setminus S$ the limit
--
--   $$\lim_{t\to\infty}x_t(\alpha)$$
--
--   exists in $\mathbb R$.
--
--   Together with Lemma 3 this gives pointwise convergence of opinions for all but countably many agents, hence almost everywhere.
--
--   **Formalization Note** "Except possibly for a countable set" is stated as the existence of a countable exceptional set $S$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Proposition 2, p. 5226

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem prop2_pointwise_convergence (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    ∃ S : Set ℝ, S.Countable ∧
      ∀ α ∈ I, α ∉ S → ∃ l : ℝ, Tendsto (fun t => x t α) atTop (𝓝 l) := by sorry

end BHTOpinion.Continuum
