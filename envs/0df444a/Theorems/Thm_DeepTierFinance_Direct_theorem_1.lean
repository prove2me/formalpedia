-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_theorem_1
-- name    : DeepTierFinance.Direct.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:26:52.136251+00:00
-- url     : https://prove2.me/theorems/cc40e301-61aa-4c10-9100-8b08e725f0f5
-- title:
--   Theorem 1 — optimal traditional contract
-- statement:
--   For any prior distribution on [0,c), there is a traditional equilibrium and, for each tier-1 capital level occurring in W, a unique emergency-cost threshold bar-e(θ₁). Its attained manufacturer optimum has the form
--
--   $$(w^*,r_m^*)=\begin{cases}(e,r_m^{PR}),&e\le\bar e(\theta_1),\(w^P,r_m^P),&e>\bar e(\theta_1).\end{cases}$$
--
--   The selected pair in each branch is a branch-specific global optimizer of the original expected Table 1 payoff; wP<e in the low branch. Complete supplier continuations, rejection, nonnegative rates, MF ties, and joint-financing deviations are retained. The threshold is quantified before varying emergency cost.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: an arbitrary distribution F on [0,c) → a Borel probability measure with mass one on [0,c) and integrable response-induced payoffs; reason: this implements the stated expectation without a density or finite-support restriction or a default nonintegrable integral
--   - encoding: terminal cash in (2)–(3) and profits in participation constraints → initial capital is subtracted from supplier cash in every adoption comparison; reason: this compares the same profit convention on both sides
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Theorem 1, printed p. 14, PDF p. 14

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem theorem_1 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∀ μ : MeasureTheory.Measure ℝ, Prior μ c →
      ∃ T : TraditionalPolicy, TraditionalEquilibrium p c μ R T ∧
        ∀ a, (∃ e, EmergencyCost p e ∧ a ∈ Set.Icc 0 (capitalUpper p (R e) c e)) →
          ∃! t, TraditionalThreshold p c μ R T a t := by sorry

end DeepTierFinance.Direct
