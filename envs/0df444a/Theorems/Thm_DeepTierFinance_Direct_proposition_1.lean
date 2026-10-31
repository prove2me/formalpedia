-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_proposition_1
-- name    : DeepTierFinance.Direct.proposition_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:06.172202+00:00
-- url     : https://prove2.me/theorems/f176bad8-a06f-4f56-b7d9-1a92db72d1f2
-- title:
--   Proposition 1 — unique financing threshold
-- statement:
--   For every w≥underline-w and r_m>0 there is a unique threshold bar-θ₂(w,r_m)≥0 such that throughout W the supplier prefers MF if and only if θ₂≤bar-θ₂. Preference compares globally optimized cash values and chooses MF on equality. Joint financing cannot exceed the better pure financing value. The threshold is nonincreasing in each of w and r_m. The existence of the response system and of the capital bounds is part of the conclusion, not a premise.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - reading: increases and decreases without a strict inequality → nondecreasing and nonincreasing comparisons; reason: the source separately writes strict inequalities where intended and the emergency branch caps investment incentives
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Proposition 1, printed p. 12, PDF p. 12

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem proposition_1 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∃ t : ℝ → Contract → ℝ,
      (∀ e, EmergencyCost p e → ∀ m, wholesaleLower p (R e) c e ≤ m.w →
        0 < m.r → FinanceThreshold p (R e) c e m (t e m) ∧
        ∀ t', FinanceThreshold p (R e) c e m t' → t' = t e m) ∧
      (∀ e, EmergencyCost p e → ∀ m m', wholesaleLower p (R e) c e ≤ m.w →
        m.w ≤ m'.w → 0 < m.r → m.r ≤ m'.r → t e m' ≤ t e m) := by sorry

end DeepTierFinance.Direct
