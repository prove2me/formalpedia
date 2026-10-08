-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_prop3a_limit_in_Fbar
-- name    : BHTOpinion.Continuum.prop3a_limit_in_Fbar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:55.997166+00:00
-- url     : https://prove2.me/theorems/c4377aee-7b38-4ec6-80c7-eb41b17188cd
-- title:
--   Proposition 3(a) — the a.e. limit of a nondecreasing solution of (3.2) lies in F̄
-- statement:
--   Let $x$ be a solution of the integral equation (3.2) such that $x_t$ is nondecreasing on $I=[0,1]$ for every $t\ge 0$, and suppose that $\tilde y(\alpha)=\lim_{t\to\infty}x_t(\alpha)$ for almost every $\alpha\in I$. Then $\tilde y\in\bar F$, in the sense that some function
--
--   $$\tilde y'\in\bar F,\qquad \tilde y'=\tilde y\ \text{ almost everywhere on } I,$$
--
--   exists. In words: every possible limit of a nondecreasing trajectory consists of opinion values that are pairwise equal or at least one unit apart, for almost every pair of agents.
--
--   **Formalization Note** The limit $\tilde y$ is determined only almost everywhere, while membership in $\bar F$ also requires $\tilde y$ to be nondecreasing at every point; the conclusion is therefore that $\tilde y$ has a representative in $\bar F$, which is how an a.e.-defined limit belongs to $\bar F$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Proposition 3(a), p. 5227

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem prop3a_limit_in_Fbar (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ)
    (hx : IsSolution x0 x) (hmono : ∀ t : ℝ, 0 ≤ t → InX (x t)) (y : ℝ → ℝ)
    (hy : ∀ᵐ α ∂(volume.restrict I), Tendsto (fun t => x t α) atTop (𝓝 (y α))) :
    ∃ y' : ℝ → ℝ, InFbar y' ∧ y' =ᵐ[volume.restrict I] y := by sorry

end BHTOpinion.Continuum
