-- Prove2me | Theorems.Thm_BlackwellDiscreteDP_Stationary_beta_optimal_frequently
-- name    : BlackwellDiscreteDP.Stationary.beta_optimal_frequently
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:00.1514+00:00
-- url     : https://prove2.me/theorems/0e730a72-bdd0-42f3-83d7-c094fa48e9bf
-- title:
--   Proof of Theorem 5 (p. 725) — some f* is β-optimal for a set of β's having 1 as a limit point
-- statement:
--   There is a decision rule $f^*$ such that $f^{*(\infty)}$ is $\beta$-optimal for a set of discount factors $\beta<1$ having $1$ as a limit point: for every $\beta_0<1$ there is $\beta\in(\beta_0,1)$ with
--
--   $$V_\beta(f^{*(\infty)})\ge V_\beta(\pi)\qquad\text{for every policy }\pi.$$
--
--   The proof of Theorem 5 starts from such an $f^*$.
-- source:
--   Blackwell, Discrete Dynamic Programming, Ann. Math. Statist. 33(2):719–726 (1962), DOI 10.1214/aoms/1177704593, p. 725, §4, proof of Theorem 5

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_Stationary_Model

namespace BlackwellDiscreteDP.Stationary

/-- §4, proof of Theorem 5, p. 725 (unnumbered; Blackwell, *Discrete Dynamic Programming*, Ann. Math. Statist. 33(2):719–726 (1962),
DOI 10.1214/aoms/1177704593):
"Let f* be β-optimal for a set of β's having 1 as a limit point."

The proof takes such an `f*` for granted; this states its existence: there is a decision rule
`f*` such that for every `β₀ < 1` some `β ∈ (β₀, 1)` makes `f*^(∞)` β-optimal against all
policies. -/
theorem beta_optimal_frequently {St Act : Type} [Fintype St] [DecidableEq St] [Nonempty St] [Fintype Act] [Nonempty Act]
    (M : Model St Act) :
    ∃ fstar : St → Act, ∀ β₀ : ℝ, β₀ < 1 →
      ∃ β : ℝ, β₀ < β ∧ β < 1 ∧ M.IsBetaOptimal β (stationary fstar) := by sorry

end BlackwellDiscreteDP.Stationary
