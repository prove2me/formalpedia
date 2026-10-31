-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_lemma_ec2
-- name    : DeepTierFinance.Direct.lemma_ec2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:08.14527+00:00
-- url     : https://prove2.me/theorems/c13b3b90-11f4-4408-bb47-f1132f2da061
-- title:
--   Lemma EC.2 — regional voluntary-adoption threshold
-- statement:
--   For each fixed admissible θ₁ and each region N∈{I,II,III,IV}, there is a threshold bar-θ₂ᴺ(θ₁|e)∈[0,c). Within that region, tier-1 adopts the blockchain menu if and only if θ₂≤bar-θ₂ᴺ. The traditional component remains the Section 4 optimal menu. The optimal blockchain menu is used for θ₂∈[0,bar-θ₂ᴺ), retaining the printed open right endpoint of clause (ii) as well as the weak endpoint in the adoption equivalence. Adoption means a strict improvement in the realized tier-1 profit.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: an arbitrary distribution F on [0,c) → a Borel probability measure with mass one on [0,c) and integrable response-induced payoffs; reason: this implements the stated expectation without a density or finite-support restriction or a default nonintegrable integral
--   - encoding: terminal cash in (2)–(3) and profits in participation constraints → initial capital is subtracted from supplier cash in every adoption comparison; reason: this compares the same profit convention on both sides
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
--   - encoding: an infinity-valued manufacturer AP rate denotes BF → Option.none denotes no manufacturer-finance offer and forces zero manufacturer principal; reason: no infinite-rate arithmetic or artificial large finite rate is introduced
--   - reading: w*, w¹*, and r_m¹* in the transition regions → the same traditional benchmark menu in all four regions; reason: the surrounding discussion identifies the Section 4 contract as the outside option
--   - encoding: the bank rate r_b*(w,theta2) is independent of tier-1 capital → the comparison uses the certified bank response at theta1=0 and the finite branch explicitly implements MF; reason: this represents the named borrowing rate without using an arbitrary zero-principal bank rate and preserves the source condition k=m
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Lemma EC.2, printed p. ec5, PDF p. 35

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem lemma_ec2 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∀ μ : MeasureTheory.Measure ℝ, Prior μ c →
      ∃ (T : TraditionalPolicy) (D : DelegatePolicy) (t₁ : ℝ → ℝ → ℝ → ℝ) (t₂ : ℝ → Contract → ℝ),
        TraditionalEquilibrium p c μ R T ∧ DelegateEquilibrium p c R T D ∧
        (∀ e, EmergencyCost p e → ∀ b ∈ Set.Ico 0 c, ∀ w,
          0 ≤ w → w ≤ 1 →
          DelegateFinanceThreshold p c R T D e w b (t₁ e w b)) ∧
        (∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
          FinanceThreshold p (R e) c e (T.menu e a) (t₂ e (T.menu e a))) ∧
        (∀ e, EmergencyCost p e → ∀ a ∈ Set.Icc 0 (capitalUpper p (R e) c e),
          ∀ N : TransitionRegion, ∃ t ∈ Set.Ico 0 c,
          ∀ b ∈ Set.Ico 0 c,
            InRegion N a b (t₁ e (D.menu e a b).w b) (t₂ e (T.menu e a)) →
            (DelegateAdopts p T D e a b 1 ↔ b ≤ t) ∧
            TraditionalOptimal p (R e) c μ T e a (T.menu e a) ∧
            (b < t → DelegateOptimal p T D e a b (D.menu e a b))) := by sorry

end DeepTierFinance.Direct
