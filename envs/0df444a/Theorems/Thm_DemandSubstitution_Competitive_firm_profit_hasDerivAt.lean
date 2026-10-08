-- Prove2me | Theorems.Thm_DemandSubstitution_Competitive_firm_profit_hasDerivAt
-- name    : DemandSubstitution.Competitive.firm_profit_hasDerivAt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:53.321726+00:00
-- url     : https://prove2.me/theorems/cbf3c8db-18b0-4e0d-a1d9-fa538adeee15
-- title:
--   §2.2, p. 8 — ∂π_i/∂Q_i = u_i − (u_i + o_i) Pr(D^s_i < Q_i)
-- statement:
--   In the competitive substitution model, fix product $i$ and the stocks $Q_{-i}$ of the other products, and regard firm $i$'s expected profit (9)
--   $$
--   \pi_i(Q_i, Q_{-i}) = E\big[u_iD^s_i - u_i(D^s_i-Q_i)^+ - o_i(Q_i-D^s_i)^+\big],\qquad D^s_i = D_i + \sum_{j\ne i} a_{ji}(D_j-Q_j)^+,
--   $$
--   as a function of $Q_i$. Assume the demand law is a probability law, absolutely continuous on $\mathbb R^n$, with positive support and integrable coordinates. Then $\pi_i$ is differentiable in $Q_i$ at every real $Q_i$, with
--   $$
--   \frac{\partial \pi_i}{\partial Q_i} = u_i - (u_i+o_i)\Pr(D^s_i<Q_i).
--   $$
--
--   This derivative is the starting point of the analysis of the competitive game: setting it to zero gives the newsvendor-type characterization (10) of best responses and of Nash equilibria.
--
--   **Formalization Note** $D^s_i$ does not involve $Q_i$, so the probability is computed with $D^s_i$ evaluated at the given vector $Q$. The statement holds at every real $Q_i$ and for arbitrary real $Q_{-i}$.
-- source:
--   Netessine & Rudi, Centralized and Competitive Inventory Models with Demand Substitution, SSRN 303779 (Simon School Working Paper OP 02-01, April 2002), p. 8, §2.2, display after (9)

import Mathlib
import Definitions.Def_DemandSubstitution_Competitive_Setting

namespace DemandSubstitution.Competitive

open MeasureTheory

/-- Netessine & Rudi (SSRN 303779), §2.2, p. 8: `∂π_i/∂Q_i = u_i − (u_i + o_i) Pr(D^s_i < Q_i)`.
`D^s_i` does not involve `Q_i`, so it is evaluated at `Q`. -/
theorem firm_profit_hasDerivAt {n : ℕ} (M : Model n) (μ : Measure (Fin n → ℝ))
    [IsProbabilityMeasure μ] (hμ : IsDemandLaw μ) (Q : Fin n → ℝ) (i : Fin n) (q : ℝ) :
    HasDerivAt (fun q' : ℝ => firmProfit M μ (Function.update Q i q') i)
      (M.u i - (M.u i + M.o i) * μ.real {x | Ds M Q x i < q}) q := by sorry

end DemandSubstitution.Competitive
