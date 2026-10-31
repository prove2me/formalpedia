-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_lemma_ec1
-- name    : DeepTierFinance.Direct.lemma_ec1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:26:39.843856+00:00
-- url     : https://prove2.me/theorems/7d15c210-7430-411b-8bc1-a2e7c5a1fe96
-- title:
--   Lemma EC.1 — optimal delegate rate threshold
-- statement:
--   Given a wholesale price w and θ₂∈[0,c), there is a unique tier-1 capital threshold. For θ₁ at or above it, the optimal fixed-price delegate rate is finite: the P rate for w<e and the PR rate for w≥e. It satisfies the corresponding printed KKT system (EC.11)–(EC.12) and is strictly less than the source bank borrowing rate r_b*(w,θ₂), certified using the bank subgame with θ₁=0. The finite branch explicitly uses MF and the no-offer branch uses BF. Below the threshold the optimal rate is infinity, meaning a BF/no-manufacturer-offer contract. Rate optimality compares all feasible rate choices using the actual sequential responses and all three strict gains. The traditional and delegate equilibria and this threshold are asserted to exist.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: an arbitrary distribution F on [0,c) → a Borel probability measure with mass one on [0,c) and integrable response-induced payoffs; reason: this implements the stated expectation without a density or finite-support restriction or a default nonintegrable integral
--   - encoding: terminal cash in (2)–(3) and profits in participation constraints → initial capital is subtracted from supplier cash in every adoption comparison; reason: this compares the same profit convention on both sides
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
--   - encoding: an infinity-valued manufacturer AP rate denotes BF → Option.none denotes no manufacturer-finance offer and forces zero manufacturer principal; reason: no infinite-rate arithmetic or artificial large finite rate is introduced
--   - encoding: real investments and reliability derivatives → P is represented on the real line, with probability and concavity constraints on nonnegative investment and derivative existence at each asserted FOC; reason: this represents the source unconstrained FOC notation and its max-with-capital boundary without discretizing investment or using an undefined derivative
--   - encoding: the bank rate r_b*(w,theta2) is independent of tier-1 capital → the comparison uses the certified bank response at theta1=0 and the finite branch explicitly implements MF; reason: this represents the named borrowing rate without using an arbitrary zero-principal bank rate and preserves the source condition k=m
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Lemma EC.1, printed p. ec4, PDF p. 34

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem lemma_ec1 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∀ μ : MeasureTheory.Measure ℝ, Prior μ c →
      ∃ T D, TraditionalEquilibrium p c μ R T ∧ DelegateEquilibrium p c R T D ∧
      ∀ e, EmergencyCost p e → ∀ b ∈ Set.Ico 0 c, ∀ w,
        0 ≤ w → w ≤ 1 →
        ∃! t, DelegateFinanceThreshold p c R T D e w b t := by sorry

end DeepTierFinance.Direct
