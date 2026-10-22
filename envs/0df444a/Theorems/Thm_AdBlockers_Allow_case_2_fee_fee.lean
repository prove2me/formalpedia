-- Prove2me | Theorems.Thm_AdBlockers_Allow_case_2_fee_fee
-- name    : AdBlockers.Allow.case_2_fee_fee
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:34.92261+00:00
-- url     : https://prove2.me/theorems/830c80fb-c3cd-4797-a06e-88a7b5864ea2
-- title:
--   Proof of Proposition 1, case 2 — (Fee, Fee): p₁ = p₂ = 1 is the unique stage-2 equilibrium, profit (λ+µ)/2 each
-- statement:
--   Let $\lambda, \mu > 0$ and suppose both platforms charge a subscription fee (the Fee plan, the same in the main model and in the benchmark). Then $p_1 = p_2 = 1$ is a stage-2 equilibrium, each platform earns
--   $$
--   r_1 = r_2 = \frac{\lambda + \mu}{2},
--   $$
--   and every stage-2 equilibrium $(p_1, p_2)$ of this subgame has $p_1 = p_2 = 1$.
--
--   This is the (Fee, Fee) entry of the benchmark payoff table (Table 1).
-- source:
--   Despotakis, Ravi & Srinivasan, The Beneficial Effects of Ad Blockers, SSRN 3083119 (version of Nov. 28, 2017), pp. 40–41, proof of Proposition 1 (Appendix A.1), case 2; Table 1, p. 17

import Mathlib
import Definitions.Def_AdBlockers_Allow_Model

namespace AdBlockers.Allow

/-- Proof of Proposition 1 (Appendix A.1), case 2, pp. 40–41 (benchmark, both platforms charge a
Fee): `p₁ = p₂ = 1` is a stage-2 equilibrium of the (Fee, Fee) subgame, each platform earns
`(λ + µ)/2`, and it is the only stage-2 equilibrium of that subgame. -/
theorem case_2_fee_fee (lam μ β γ : ℝ) (hlam : 0 < lam) (hμ : 0 < μ) :
    IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 ∧
      rev₁ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 = (lam + μ) / 2 ∧
      rev₂ lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan 1 1 = (lam + μ) / 2 ∧
      ∀ p₁ p₂ : ℝ, IsStage2NE lam μ β γ BenchPlan.fee.toPlan BenchPlan.fee.toPlan p₁ p₂ →
        p₁ = 1 ∧ p₂ = 1 := by sorry

end AdBlockers.Allow
