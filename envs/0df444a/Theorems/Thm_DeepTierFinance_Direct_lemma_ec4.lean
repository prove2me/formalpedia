-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_lemma_ec4
-- name    : DeepTierFinance.Direct.lemma_ec4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:26.835258+00:00
-- url     : https://prove2.me/theorems/fa3d19c7-11c1-4532-a143-8736e06357d5
-- title:
--   Lemma EC.4 — manufacturer-financed supplier response
-- statement:
--   In the source capital region W, for every w≥underline-w and r_m≥0, the MF optimum is implemented by
--
--   $$r_s^*=z^{*-1}\bigl(\max\{y^{m*},\theta_1+\theta_2\}\mid\theta_2\bigr),$$
--
--   where the target ym* solves (EC.2), the source's FOC of (3). The response is globally optimal and its implemented investment is unique. The target is nondecreasing in w, θ₁ and θ₂ and nonincreasing in r_m. At fixed r_m the implementing rate is nonincreasing in w, θ₁ and θ₂. The optimized terminal cash equals the source's objective evaluated at ym*; it is nondecreasing in w and nonincreasing in r_m. All comparisons retain their complete admissible real domains.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: real investments and reliability derivatives → P is represented on the real line, with probability and concavity constraints on nonnegative investment and derivative existence at each asserted FOC; reason: this represents the source unconstrained FOC notation and its max-with-capital boundary without discretizing investment or using an undefined derivative
--   - reading: increases and decreases without a strict inequality → nondecreasing and nonincreasing comparisons; reason: the source separately writes strict inequalities where intended and the emergency branch caps investment incentives
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Lemma EC.4, printed p. ec10–ec11, PDF p. 40

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem lemma_ec4 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧
      ∃ target : ℝ → ℝ → ℝ → Contract → ℝ,
      (∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
        ∀ m, wholesaleLower p (R e) c e ≤ m.w → 0 ≤ m.r →
        ManufacturerFOC p m.w m.r a b (target e a b m) ∧
        offerCash p (R e).investment e a b m .manufacturer ((R e).manufacturer e a b m) =
          tier1Cash p e m.w a b (inverseRate p b (target e a b m)) m.r (target e a b m) ∧
        ImplementedInverse p (R e).investment b ((R e).manufacturer e a b m).rs
          (max (target e a b m) (a + b)) ∧
        (∀ q, OfferOptimal p (R e).investment e a b m .manufacturer q →
          (R e).investment b q.rs = max (target e a b m) (a + b))) ∧
      (∀ e, EmergencyCost p e → ∀ a b a' b',
        CapitalRegion p (R e) c e a b → CapitalRegion p (R e) c e a' b' →
        ∀ m m', wholesaleLower p (R e) c e ≤ m.w → 0 ≤ m.r →
        wholesaleLower p (R e) c e ≤ m'.w → 0 ≤ m'.r →
        a ≤ a' → b ≤ b' → m.w ≤ m'.w → m'.r ≤ m.r →
        target e a b m ≤ target e a' b' m') ∧
      (∀ e, EmergencyCost p e → ∀ a b a' b',
        CapitalRegion p (R e) c e a b → CapitalRegion p (R e) c e a' b' →
        ∀ m m', wholesaleLower p (R e) c e ≤ m.w → 0 ≤ m.r →
        wholesaleLower p (R e) c e ≤ m'.w → 0 ≤ m'.r →
        a ≤ a' → b ≤ b' → m.w ≤ m'.w → m.r = m'.r →
        ((R e).manufacturer e a' b' m').rs ≤ ((R e).manufacturer e a b m).rs) ∧
      (∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
        ∀ m m', wholesaleLower p (R e) c e ≤ m.w → 0 ≤ m.r →
        wholesaleLower p (R e) c e ≤ m'.w → 0 ≤ m'.r → m.w ≤ m'.w → m'.r ≤ m.r →
        offerCash p (R e).investment e a b m .manufacturer ((R e).manufacturer e a b m) ≤
        offerCash p (R e).investment e a b m' .manufacturer ((R e).manufacturer e a b m')) := by sorry

end DeepTierFinance.Direct
