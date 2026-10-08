-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_theorem5_convergence
-- name    : BHTOpinion.Continuum.theorem5_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:04.108882+00:00
-- url     : https://prove2.me/theorems/3c32a86c-c57b-4f3c-9d77-45862d299a65
-- title:
--   Theorem 5 — x_t → ỹ ∈ F̄ almost everywhere, and F ⊆ {nondecreasing fixed points} ⊆ F̄
-- statement:
--   Let $x$ be a solution of the integral equation (3.2) such that $x_0$ is regular or, more generally, such that $x_t$ is nondecreasing on $I=[0,1]$ for every $t\ge 0$. Then:
--
--   1. there is a function $\tilde y\in\bar F$ such that
--   $$\lim_{t\to\infty}x_t(\alpha)=\tilde y(\alpha)\quad\text{for almost every }\alpha\in I;$$
--   2. every $\tilde s\in F$ is a nondecreasing fixed point;
--   3. every nondecreasing fixed point belongs to $\bar F$.
--
--   This summarizes the convergence theory of the continuum model: opinions converge to configurations whose distinct values are, for almost every pair of agents, at least one unit apart.
--
--   **Formalization Note** The two cases of the hypothesis ("$x_0$ is regular, or more generally $x_t$ nondecreasing for all $t$") are a disjunction; $x_0$ is the solution at time $0$. Parts 2 and 3 are the set inclusions of the paper's last sentence and do not depend on $x$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Theorem 5, p. 5228

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem theorem5_convergence (x0 : ℝ → ℝ) (x : ℝ → ℝ → ℝ) (hx : IsSolution x0 x)
    (hreg : Regular (x 0) ∨ ∀ t : ℝ, 0 ≤ t → InX (x t)) :
    (∃ y : ℝ → ℝ, InFbar y ∧
      ∀ᵐ α ∂(volume.restrict I), Tendsto (fun t => x t α) atTop (𝓝 (y α))) ∧
    {s : ℝ → ℝ | InF s} ⊆ {s | InX s ∧ IsFixedPoint s} ∧
    {s : ℝ → ℝ | InX s ∧ IsFixedPoint s} ⊆ {s | InFbar s} := by sorry

end BHTOpinion.Continuum
