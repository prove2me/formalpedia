-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_theorem_2
-- name    : DeepTierFinance.Direct.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:14.739138+00:00
-- url     : https://prove2.me/theorems/8a548f2e-415a-4c95-be88-14d9436a951a
-- title:
--   Theorem 2 — optimal delegate menu and adoption
-- statement:
--   For an arbitrary prior, the traditional and delegate equilibria exist. For every θ₁ there is a capital threshold bar-hat-θ₂(θ₁|e)∈[0,c). Both suppliers adopt if and only if θ₂≤bar-hat-θ₂. In that region the optimal menu is (e,hat-r_m^{1PR*}) if e≤bar-hat-e(θ₁,θ₂), and the optimal P-branch pair otherwise. Above the capital threshold it is exactly the traditional menu (w*,r_m*). Branch candidates optimize the original problem whenever their feasible branch is nonempty. The emergency threshold is independent of e and identifies actual emergency sourcing in the adoption region. For each branch I∈{P,PR}, the rate is infinity if θ₁≤bar-θ₁, indicating BF; this printed weak endpoint is retained despite the finite-branch weak endpoint of Lemma EC.1. Every adopted contract is an attained global maximum under strict improvement for all three agents.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: an arbitrary distribution F on [0,c) → a Borel probability measure with mass one on [0,c) and integrable response-induced payoffs; reason: this implements the stated expectation without a density or finite-support restriction or a default nonintegrable integral
--   - encoding: terminal cash in (2)–(3) and profits in participation constraints → initial capital is subtracted from supplier cash in every adoption comparison; reason: this compares the same profit convention on both sides
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
--   - encoding: an infinity-valued manufacturer AP rate denotes BF → Option.none denotes no manufacturer-finance offer and forces zero manufacturer principal; reason: no infinite-rate arithmetic or artificial large finite rate is introduced
--   - reading: the abbreviated capital threshold bar-theta1(theta2) in Theorem 2 → the fixed-price threshold is evaluated at the corresponding branch wholesale price; reason: Lemma EC.1 defines the threshold as bar-theta1(w,theta2); the printed equality directions are preserved
--   - encoding: the bank rate r_b*(w,theta2) is independent of tier-1 capital → the comparison uses the certified bank response at theta1=0 and the finite branch explicitly implements MF; reason: this represents the named borrowing rate without using an arbitrary zero-principal bank rate and preserves the source condition k=m
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Theorem 2, printed p. 18, PDF p. 18

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem theorem_2 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∀ μ : MeasureTheory.Measure ℝ, Prior μ c →
      ∃ (T : TraditionalPolicy) (D : DelegatePolicy) (tAdopt : ℝ → ℝ → ℝ) (tEmergency : ℝ → ℝ → ℝ)
          (tFinance : ℝ → ℝ → ℝ → ℝ)
          (low high : ℝ → ℝ → ℝ → BlockchainContract),
        TraditionalEquilibrium p c μ R T ∧ DelegateEquilibrium p c R T D ∧
        (∀ a b, DelegateEmergencyThreshold p c R T D a b (tEmergency a b)) ∧
        (∀ e, EmergencyCost p e → ∀ b ∈ Set.Ico 0 c, ∀ w,
          0 ≤ w → w ≤ 1 →
          DelegateFinanceThreshold p c R T D e w b (tFinance e w b)) ∧
        (∀ e, EmergencyCost p e → ∀ a ∈ Set.Icc 0 (capitalUpper p (R e) c e),
          tAdopt e a ∈ Set.Ico 0 c ∧ ∀ b ∈ Set.Ico 0 c,
          (high e a b).w = e ∧ 0 ≤ (low e a b).w ∧ (low e a b).w < e ∧
          ((∃ n, DelegateFeasible p T D e a b n ∧ n.w < e) →
            DelegateBranch p T D e a b false (low e a b)) ∧
          ((∃ n, DelegateFeasible p T D e a b n ∧ e ≤ n.w) →
            DelegateBranch p T D e a b true (high e a b)) ∧
          (DelegateAdopts p T D e a b 1 ↔ b ≤ tAdopt e a) ∧
          (DelegateAdopts p T D e a b 2 ↔ b ≤ tAdopt e a) ∧
          (if b ≤ tAdopt e a then
            (if e ≤ tEmergency a b then
              D.menu e a b = high e a b ∧ (high e a b).w = e ∧
                DelegateBranch p T D e a b true (high e a b)
             else D.menu e a b = low e a b ∧
                DelegateBranch p T D e a b false (low e a b))
           else D.menu e a b = (T.menu e a).finite) ∧
          (a ≤ tFinance e (low e a b).w b → (low e a b).rate = none) ∧
          (a ≤ tFinance e (high e a b).w b → (high e a b).rate = none)) := by sorry

end DeepTierFinance.Direct
