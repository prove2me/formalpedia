-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_proposition_ec1
-- name    : DeepTierFinance.Direct.proposition_ec1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:16.254178+00:00
-- url     : https://prove2.me/theorems/7ee929e4-e526-4801-a6eb-ab82e3f3ea49
-- title:
--   Proposition EC.1 — four financing transitions
-- statement:
--   At an equilibrium profile adopting blockchain, let t₁ be the fixed-price delegate financing threshold evaluated at the optimal blockchain wholesale price and let t₂ be the traditional financing threshold at the benchmark contract. The four transitions are:
--
--   1. Region I: θ₁<t₁ and θ₂>t₂ gives BF to BF.
--   2. Region II: θ₁≥t₁ and θ₂≤t₂ gives MF to MF.
--   3. Region III: θ₁<t₁ and θ₂≤t₂ gives MF to BF.
--   4. Region IV: θ₁≥t₁ and θ₂>t₂ gives BF to MF.
--
--   The thresholds are certified by their underlying optimization problems, not free region labels. Traditional and delegate equilibria are existential conclusions.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: an arbitrary distribution F on [0,c) → a Borel probability measure with mass one on [0,c) and integrable response-induced payoffs; reason: this implements the stated expectation without a density or finite-support restriction or a default nonintegrable integral
--   - encoding: terminal cash in (2)–(3) and profits in participation constraints → initial capital is subtracted from supplier cash in every adoption comparison; reason: this compares the same profit convention on both sides
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
--   - encoding: an infinity-valued manufacturer AP rate denotes BF → Option.none denotes no manufacturer-finance offer and forces zero manufacturer principal; reason: no infinite-rate arithmetic or artificial large finite rate is introduced
--   - reading: w*, w¹*, and r_m¹* in the transition regions → the same traditional benchmark menu in all four regions; reason: the surrounding discussion identifies the Section 4 contract as the outside option
--   - reading: from no-blockchain to blockchain adoption in equilibrium → financing transitions are asserted at profiles that actually adopt; reason: the phrase identifies a comparison conditional on adoption; the later adoption lemma determines which profiles adopt
--   - encoding: the bank rate r_b*(w,theta2) is independent of tier-1 capital → the comparison uses the certified bank response at theta1=0 and the finite branch explicitly implements MF; reason: this represents the named borrowing rate without using an arbitrary zero-principal bank rate and preserves the source condition k=m
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Proposition EC.1, printed p. ec4–ec5, PDF p. 34

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem proposition_ec1 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∀ μ : MeasureTheory.Measure ℝ, Prior μ c →
      ∃ (T : TraditionalPolicy) (D : DelegatePolicy) (t₁ : ℝ → ℝ → ℝ → ℝ) (t₂ : ℝ → Contract → ℝ),
        TraditionalEquilibrium p c μ R T ∧ DelegateEquilibrium p c R T D ∧
        (∀ e, EmergencyCost p e → ∀ b ∈ Set.Ico 0 c, ∀ w,
          0 ≤ w → w ≤ 1 →
          DelegateFinanceThreshold p c R T D e w b (t₁ e w b)) ∧
        (∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
          FinanceThreshold p (R e) c e (T.menu e a) (t₂ e (T.menu e a))) ∧
        (∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
          DelegateAdopts p T D e a b 1 →
          let old := T.response e a b (T.menu e a)
          let new := D.response e a b (D.menu e a b)
          let x := t₁ e (D.menu e a b).w b
          let z := t₂ e (T.menu e a)
          (InRegion .I a b x z → old.financing = .bank ∧ new.financing = .bank) ∧
          (InRegion .II a b x z → old.financing = .manufacturer ∧ new.financing = .manufacturer) ∧
          (InRegion .III a b x z → old.financing = .manufacturer ∧ new.financing = .bank) ∧
          (InRegion .IV a b x z → old.financing = .bank ∧ new.financing = .manufacturer)) := by sorry

end DeepTierFinance.Direct
