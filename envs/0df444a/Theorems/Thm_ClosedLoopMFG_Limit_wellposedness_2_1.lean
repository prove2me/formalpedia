-- Prove2me | Theorems.Thm_ClosedLoopMFG_Limit_wellposedness_2_1
-- name    : ClosedLoopMFG.Limit.wellposedness_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:32:03.968526+00:00
-- url     : https://prove2.me/theorems/ba50abb2-460f-44ce-aef0-324c8ebc7fc8
-- title:
--   §2.1, p. 6 — the $n$-player state system has a unique in law solution
-- statement:
--   Assume Assumption A. Let $n\ge1$ and let $\alpha=(\alpha^1,\dots,\alpha^n)$ be a profile of admissible closed-loop controls. Then the state system
--   $$dX^i_t=b\big(t,X^i_t,\mu^n_t,\alpha^i(t,X)\big)\,dt+dW^i_t,\qquad\mu^n_t=\frac1n\sum_{k=1}^n\delta_{X^k_t},\qquad i=1,\dots,n,$$
--   with $W^1,\dots,W^n$ independent Brownian motions and $X^1_0,\dots,X^n_0$ i.i.d. with law $\lambda$, independent of the Brownian motions, has a weak solution, and any two weak solutions give $X=(X^1,\dots,X^n)$ the same law on $(\mathcal C^d)^n$.
--
--   The paper justifies this "by Girsanov's theorem". It is what makes the payoffs $J^n_i$, and hence the Nash property and the law of $\mu^n[\alpha]$, well defined.
--
--   **Formalization Note** Weak solutions are the structures `NSol` of the `Game` file; the drift is bounded because $b$ is bounded on $[0,T]\times\mathbb R^d\times\mathcal P(\mathbb R^d)\times A$ and the controls take values in $A$ on $[0,T]$.
-- source:
--   Lacker, On the convergence of closed-loop Nash equilibria to the mean field game limit, arXiv:1808.02745v1, p. 6, Section 2.1

import Mathlib
import Definitions.Def_ClosedLoopMFG_Limit_Model
import Definitions.Def_ClosedLoopMFG_Limit_Game

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace ClosedLoopMFG.Limit

/-- **§2.1, p. 6: the `n`-player state system is well posed in law.** Under Assumption A, for every
profile of admissible controls the state system has a weak solution, and any two weak solutions
give the state vector `X = (X^1, …, X^n)` the same law on `(𝒞^d)^n`. -/
theorem wellposedness_2_1 {d : ℕ} {T : ℝ≥0} (hT : 0 < T) {EA : Type} [NormedAddCommGroup EA]
    [NormedSpace ℝ EA] [MeasurableSpace EA] [BorelSpace EA] (A : Set EA) (lam : PR d)
    (b : ℝ → E d → PR d → EA → E d) (f : ℝ → E d → PR d → EA → ℝ) (g : E d → PR d → ℝ)
    (hA : AssumptionA T A b f g)
    {n : ℕ} [NeZero n] (α : Fin n → ℝ → (Fin n → Path d T) → EA)
    (hα : ∀ i, IsAdmissible A (α i)) :
    Nonempty (NSol n d T lam (drift b α)) ∧
    ∀ S S' : NSol n d T lam (drift b α), S.P.map S.X = S'.P.map S'.X := by sorry

end ClosedLoopMFG.Limit
