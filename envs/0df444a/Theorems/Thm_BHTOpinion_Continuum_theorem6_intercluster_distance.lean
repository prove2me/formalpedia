-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_theorem6_intercluster_distance
-- name    : BHTOpinion.Continuum.theorem6_intercluster_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:00.564439+00:00
-- url     : https://prove2.me/theorems/93aef5f4-5109-42dc-b91d-0379df2d9ca5
-- title:
--   Theorem 6 — for regular x̃_0, any two clusters of the limit satisfy |B − A| ≥ 1 + min{W_A, W_B}/max{W_A, W_B}
-- statement:
--   Let $\tilde x_0$ be a regular initial opinion function on $I=[0,1]$ (nondecreasing, with increase rate between $m$ and $M$ for some $m,M>0$), let $x$ be a solution of the integral equation (3.2) with initial condition $\tilde x_0$, and let $\tilde s$ be a function with $\tilde s(\alpha)=\lim_{t\to\infty}x_t(\alpha)$ for almost every $\alpha\in I$. A **cluster** of $\tilde s$ is a value $A$ held by a set of agents of positive Lebesgue measure $W_A$. Then:
--
--   1. for any two distinct clusters $A\ne B$ of $\tilde s$,
--   $$|B-A|\ \ge\ 1+\frac{\min\{W_A,W_B\}}{\max\{W_A,W_B\}};$$
--   2. $\tilde s$ belongs to $F$ and is a fixed point, in the sense that some $\tilde s'\in F$ equals $\tilde s$ almost everywhere on $I$ and $\tilde s'$ is a fixed point.
--
--   Thus a continuum of agents with regular initial opinions does not merely split into clusters at least one unit apart: two clusters must be further apart the more balanced their weights are, up to distance $2$ for clusters of equal weight. This is the continuum analogue of the stability condition for the discrete-agent model.
--
--   **Formalization Note** "The solution" of (3.2) is taken to be any solution; by Theorem 4 there is exactly one. The limit $\tilde s$ is a hypothesis, as on the page ("let $\tilde s$ be the function to which $x$ converges"); its existence is Theorem 5. "Any two clusters" means two distinct clusters with positive weights (for $A=B$ the inequality would read $0\ge2$). Since $\tilde s$ is defined only almost everywhere while $F$ is a pointwise condition, "$\tilde s$ belongs to $F$ and is a fixed point" is stated for an a.e.-equal representative. Weights are measures of level sets, so they do not depend on the choice of representative.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Theorem 6 and (3.12), p. 5228; clusters and weights defined p. 5228

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem theorem6_intercluster_distance (x0 : ℝ → ℝ) (hreg : Regular x0)
    (x : ℝ → ℝ → ℝ) (hx : IsSolution x0 x) (s : ℝ → ℝ)
    (hs : ∀ᵐ α ∂(volume.restrict I), Tendsto (fun t => x t α) atTop (𝓝 (s α))) :
    (∀ A B : ℝ, A ≠ B → IsCluster s A → IsCluster s B →
      1 + min (weight s A) (weight s B) / max (weight s A) (weight s B) ≤ |B - A|) ∧
    ∃ s' : ℝ → ℝ, InF s' ∧ s' =ᵐ[volume.restrict I] s ∧ IsFixedPoint s' := by sorry

end BHTOpinion.Continuum
