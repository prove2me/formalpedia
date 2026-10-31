-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_lemma_1
-- name    : DeepTierFinance.Direct.lemma_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:21:31.923223+00:00
-- url     : https://prove2.me/theorems/98ccd0f6-83b5-49c4-85a3-a06114772b31
-- title:
--   Lemma 1 — optimal investment and AP amount
-- statement:
--   For the Section 3 increasing concave reliability technology and procurement price, the source's unconstrained investment optimum c exists uniquely. For each θ₂∈[0,c) and AP rate r_s>0, there are a solution z* of (1) and an actual global optimal investment y* such that
--
--   $$y^*=\max\{z^*,\theta_2\},\qquad B_s^*=(y^*-\theta_2)^+=y^*-\theta_2.$$
--
--   The investment maximizes the self-funding/limited-liability borrowing cash flow and permits retaining initial capital. No upper cap c is placed on the borrowing investment.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: real investments and reliability derivatives → P is represented on the real line, with probability and concavity constraints on nonnegative investment and derivative existence at each asserted FOC; reason: this represents the source unconstrained FOC notation and its max-with-capital boundary without discretizing investment or using an undefined derivative
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Lemma 1, printed p. 10, PDF p. 10

import Definitions.Def_DeepTierFinance_Direct_Primitives

namespace DeepTierFinance.Direct

theorem lemma_1
    (p : DeepTierFinance.Direct.Primitives) (hp : p.Valid) :
    ∃ c : ℝ, DeepTierFinance.Direct.CapitalOptimum p c ∧
      ∀ θ ∈ Set.Ico 0 c, ∀ r : ℝ, 0 < r →
        ∃ z y : ℝ, DeepTierFinance.Direct.InvestmentFOC p θ r z ∧
          DeepTierFinance.Direct.InvestmentResponse p θ r y ∧
          y = max z θ ∧ DeepTierFinance.Direct.advance θ y = y - θ := by sorry

end DeepTierFinance.Direct
