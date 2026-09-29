-- Prove2me | Theorems.Thm_BertsekasDP_pontryagin_minimum_principle
-- name    : BertsekasDP.pontryagin_minimum_principle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-07T15:47:22.768348+00:00
-- url     : https://prove2.me/theorems/e930c46c-da0d-444a-b3d0-b4996208ca58
-- title:
--   Pontryagin Minimum Principle (Prop. 3.3.1)
-- statement:
--   **Proposition 3.3.1 (Pontryagin Minimum Principle).** Consider the continuous-time problem of minimizing $h(x(T)) + \int_0^T g(x,u)\,dt$ subject to $\dot x = f(x,u)$, $x(0) = x_0$ and $u(t) \in U$, with $f$, $g$ and $h$ continuously differentiable. Let $\{u^*(t) \mid t \in [0,T]\}$ be an optimal admissible control trajectory and $\{x^*(t)\}$ the corresponding state trajectory. Then there is an adjoint trajectory $p$, continuous on $[0,T]$, satisfying the **adjoint equation** and its terminal condition
--
--   $$\dot p(t) \;=\; -\nabla_x H\bigl(x^*(t), u^*(t), p(t)\bigr), \qquad p(T) \;=\; \nabla h\bigl(x^*(T)\bigr),$$
--
--   such that the control minimizes the Hamiltonian pointwise,
--
--   $$u^*(t) \;\in\; \arg\min_{u \in U} \; H\bigl(x^*(t), u, p(t)\bigr),$$
--
--   and the Hamiltonian is constant along the optimal trajectory,
--
--   $$H\bigl(x^*(t), u^*(t), p(t)\bigr) \;=\; c \qquad \text{for all } t,$$
--
--   for some constant $c$. Here $H(x,u,p) = g(x,u) + \langle p, f(x,u)\rangle$.
--
--   The Minimum Principle converts an optimization over a function space into a two-point boundary value problem in $2n$ ordinary differential equations — the basis of shooting methods and of every bang-bang analysis. Its conditions are necessary, not sufficient: a trajectory satisfying them need not be optimal, and further argument (existence plus uniqueness of the candidate, or convexity) is needed to conclude optimality.
--
--   **Formalization Note** The three conditions hold off a common finite exceptional set, which is where the piecewise continuous control switches; this is the precise reading of the source's "for all $t \in [0,T]$" in the presence of switching. Constancy of the Hamiltonian uses time-independence of $f$ and $g$, as the source notes it may fail otherwise. Uniqueness of $p$ is not asserted, and the terminal condition fixes the cost multiplier at $1$, so no abnormal multiplier appears.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 3.3.1

import Mathlib
import Definitions.Def_BertsekasCTModel

namespace BertsekasDP

theorem pontryagin_minimum_principle {n m : ℕ} (M : BertsekasCTModel n m)
    (hf : ContDiff ℝ 1 (Function.uncurry M.f))
    (hg : ContDiff ℝ 1 (Function.uncurry M.g))
    (hh : ContDiff ℝ 1 M.h)
    (ustar : ℝ → EuclideanSpace ℝ (Fin m))
    (xstar : ℝ → EuclideanSpace ℝ (Fin n))
    (hadm : BertsekasCTAdmissibleFrom M 0 M.x0 ustar xstar)
    (hopt : ∀ u x, BertsekasCTAdmissibleFrom M 0 M.x0 u x →
      BertsekasCTCostFrom M 0 ustar xstar ≤ BertsekasCTCostFrom M 0 u x) :
    ∃ (p : ℝ → EuclideanSpace ℝ (Fin n)) (F : Finset ℝ) (c : ℝ),
      ContinuousOn p (Set.Icc 0 M.T) ∧
      p M.T = gradient M.h (xstar M.T) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        HasDerivAt p
          (-gradient (fun y => BertsekasHamiltonian M y (ustar t) (p t)) (xstar t))
          t) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        IsMinOn (fun u => BertsekasHamiltonian M (xstar t) u (p t)) M.U (ustar t)) ∧
      (∀ t ∈ Set.Icc 0 M.T \ (F : Set ℝ),
        BertsekasHamiltonian M (xstar t) (ustar t) (p t) = c) := by sorry

end BertsekasDP
