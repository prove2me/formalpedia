-- Prove2me | Theorems.Thm_BHTOpinion_Approx_Supplement_theorem1_almost_all_proper
-- name    : BHTOpinion.Approx.Supplement.theorem1_almost_all_proper
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T05:54:53.677419+00:00
-- url     : https://prove2.me/theorems/0e481bd9-f640-4e47-b748-0d5112de664c
-- title:
--   Theorem 1 — Lebesgue-almost every x̃ ∈ ℝⁿ is a proper initial condition of (2.1)
-- statement:
--   Fix a number $n$ of agents, interacting through (2.1),
--   $$
--   x_i(t)=x_i(0)+\int_0^t\sum_{j:\,|x_i(\tau)-x_j(\tau)|<1}\bigl(x_j(\tau)-x_i(\tau)\bigr)\,d\tau .
--   $$
--   A vector $\tilde x\in\mathbb R^n$ is a **proper initial condition** if (a) there is a unique solution $x$ of (2.1) on $[0,\infty)$ with $x(0)=\tilde x$; (b) the set of times at which $x$ is not differentiable is at most countable and has no accumulation point; (c) if $x_i(t)=x_j(t)$ for some $t$, then $x_i(t')=x_j(t')$ for every $t'\ge t$.
--
--   **Theorem 1.** For Lebesgue-almost every $\tilde x\in\mathbb R^n$,
--   $$
--   \exists\,x \text{ with } x(0)=\tilde x \text{ that is a proper solution of (2.1)} .
--   $$
--
--   No sortedness or distinctness of the coordinates of $\tilde x$ is assumed. The theorem justifies restricting the rest of the paper (convergence, Theorem 2; approximation of the continuum model, Theorem 7) to proper initial conditions.
--
--   **Formalization Note** The predicate is the published `BHTOpinion.Approx.IsProperDiscreteSolution`: a solution of (2.1), unique among solutions with the same initial value on $[0,\infty)$, whose non-differentiability times meet every $[0,T]$ in a finite set, and with persistent coordinate equalities. The measure is `volume` on `Fin n → ℝ`, the $n$-dimensional Lebesgue measure.
--
--   Differences from the source:
--   - encoding: (b) the non-differentiability set is at most countable and has no accumulation points → its intersection with every [0, T] is finite (the published IsProperDiscreteSolution); reason: for a subset of [0, ∞) the two conditions are equivalent
--   - encoding: almost all x̃ ∈ ℜⁿ (Lebesgue measure) → ∀ᵐ x̃ ∂volume on Fin n → ℝ: the exceptional set is contained in a Lebesgue-null set; reason: Lean's almost-everywhere filter; no measurability of the set of proper initial conditions is asserted or assumed
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), DOI 10.1137/090766188, Theorem 1, p. 5218 (PDF 5); definition of proper initial conditions p. 5218; proof sketch Appendix A, pp. 5234–5236 (PDF 21–23)

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Discrete

namespace BHTOpinion.Approx.Supplement

theorem theorem1_almost_all_proper (n : ℕ) :
    ∀ᵐ x₀ : Fin n → ℝ ∂MeasureTheory.volume,
      ∃ x : ℝ → Fin n → ℝ, x 0 = x₀ ∧ BHTOpinion.Approx.IsProperDiscreteSolution x := by sorry

end BHTOpinion.Approx.Supplement
