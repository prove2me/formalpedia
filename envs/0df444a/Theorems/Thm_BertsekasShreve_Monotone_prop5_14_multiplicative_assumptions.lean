-- Prove2me | Theorems.Thm_BertsekasShreve_Monotone_prop5_14_multiplicative_assumptions
-- name    : BertsekasShreve.Monotone.prop5_14_multiplicative_assumptions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:20:20.611678+00:00
-- url     : https://prove2.me/theorems/440de10b-9062-46a4-be4e-e0d6bd89b974
-- title:
--   Proposition 5.14 — the multiplicative-cost model satisfies I, I.1, I.2 (scalar b) or D, D.1, D.2 (scalar 1)
-- statement:
--   Let $W$ be a countable set, $p(\cdot\mid x,u)$ a probability distribution on $W$ for each $(x,u)\in S\times C$, $g : S\times C\times W\to[-\infty,\infty]$ and $f : S\times C\times W\to S$. Consider an abstract monotone dynamic programming model on $S$, $C$ with constraint sets $U(x)$ whose mapping is the multiplicative-cost mapping
--   $$H(x,u,J)=E\{\,g(x,u,w)\,J[f(x,u,w)]\mid x,u\,\}$$
--   (the expectation of Section 2.3.2 on the countable set $W$: positive and negative parts summed separately, with $\infty-\infty=\infty$) and whose terminal function is $J_0(x)=1$ for all $x\in S$.
--
--   1. If there is $b\in\mathbb R$ with
--   $$1\le g(x,u,w)\le b\qquad\forall x\in S,\ u\in U(x),\ w\in W,$$
--   then Assumptions I, I.1 and I.2 are satisfied, with the scalar in I.2 equal to $b$.
--   2. If
--   $$0\le g(x,u,w)\le 1\qquad\forall x\in S,\ u\in U(x),\ w\in W,$$
--   then Assumptions D, D.1 and D.2 are satisfied, with the scalar in D.2 equal to $1$.
--
--   Consequently every result of the chapter proved under I, I.1, I.2 (respectively D, D.1, D.2) applies to stochastic control problems with a multiplicative cost functional, such as the risk-sensitive exponential cost.
--
--   **Formalization Note** Part 1 is stated for every `MonotoneDP.Increase.Model` and part 2 for every `MonotoneDP.Decrease.Model` whose fields are `H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f` (the shared definition of Section 2.3.4's mapping, with the book's expectation `expect`) and `Jbar ≡ 1`; monotonicity of $H$, part of the model, holds under either hypothesis because $g\ge0$ (Section 2.3.4, eq. (27)), so such models exist. $W$ is `[Countable W]` and each $p(\cdot\mid x,u)$ is a `PMF W`.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 90, Proposition 5.14; mapping from p. 37, Section 2.3.4, Eq. (26) of Chapter 2

import Mathlib
import Definitions.Def_MonotoneDP_Increase_Model
import Definitions.Def_MonotoneDP_Increase_Assumptions
import Definitions.Def_MonotoneDP_Decrease_Model
import Definitions.Def_MonotoneDP_Decrease_Assumptions
import Definitions.Def_BertsekasShreve_FiniteHorizon_SpecificModels

namespace BertsekasShreve.Monotone

/-- Bertsekas & Shreve (1996), p. 90, Proposition 5.14: for the multiplicative mapping
`H(x, u, J) = E{g(x, u, w) J[f(x, u, w)] | x, u}` of Section 2.3.4 (countable `W`) with
`J₀ ≡ 1`:
(a) if `1 ≤ g(x, u, w) ≤ b` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, with `b ∈ ℝ`, then I, I.1 and I.2
hold, the scalar in I.2 being `b`;
(b) if `0 ≤ g(x, u, w) ≤ 1` for all `x ∈ S`, `u ∈ U(x)`, `w ∈ W`, then D, D.1 and D.2 hold, the
scalar in D.2 being `1`.
A model of Part I with this `H` and `J₀` is any `Model` whose fields `H` and `Jbar` are these. -/
theorem prop5_14_multiplicative_assumptions {S C W : Type*} [Countable W]
    (p : S → C → PMF W) (g : S → C → W → EReal) (f : S → C → W → S) :
    (∀ m : MonotoneDP.Increase.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      ∀ b : ℝ, (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 1 ≤ g x u w ∧ g x u w ≤ (b : EReal)) →
        m.AssumptionI ∧ m.AssumptionI1 ∧ m.AssumptionI2 b) ∧
    (∀ m : MonotoneDP.Decrease.Model S C, m.H = BertsekasShreve.FiniteHorizon.multiplicativeH p g f → m.Jbar = (fun _ => 1) →
      (∀ x : S, ∀ u ∈ m.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ 1) →
        m.AssumptionD ∧ m.AssumptionD1 ∧ m.AssumptionD2 1) := by sorry

end BertsekasShreve.Monotone
