-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_lemma_ec3
-- name    : DeepTierFinance.Direct.lemma_ec3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:17.360925+00:00
-- url     : https://prove2.me/theorems/53ede29b-f77e-4e16-b2eb-d2f0c5a12625
-- title:
--   Lemma EC.3 — bank-financed supplier response
-- statement:
--   For every θ₂∈[0,c), θ₁≥0, and tier-0 wholesale price w≥underline-w, the optimal BF offer implements the unique optimal target yb* through the inverse of (1), and that target solves (EC.1), the FOC of (2). The implementing AP rate and target investment are independent of θ₁. Increasing the wholesale price weakly decreases the AP rate, weakly increases investment, and weakly increases the optimized tier-1 terminal cash. Investment incentives use min(w,e), as in the source's emergency-price cap. The theorem asserts the existence of the actual response functions and certifies their global cash optimality rather than defining them by the FOC.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: real investments and reliability derivatives → P is represented on the real line, with probability and concavity constraints on nonnegative investment and derivative existence at each asserted FOC; reason: this represents the source unconstrained FOC notation and its max-with-capital boundary without discretizing investment or using an undefined derivative
--   - reading: increases and decreases without a strict inequality → nondecreasing and nonincreasing comparisons; reason: the source separately writes strict inequalities where intended and the emergency branch caps investment incentives
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Lemma EC.3, printed p. ec10, PDF p. 40

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem lemma_ec3 (p : Primitives) (hp : p.Valid) :
    ∃ c : ℝ, CapitalOptimum p c ∧ ∀ e, EmergencyCost p e →
      ∃ s : Responses, InvestmentRational p c s.investment ∧ BoundaryResponses p s c e ∧
        (∀ w, wholesaleLower p s c e ≤ w → ∀ b ∈ Set.Ico 0 c,
          ∀ a, 0 ≤ a →
          OfferOptimal p s.investment e a b ⟨w, 0⟩ .bank (s.bank e w a b) ∧
          ImplementedInverse p s.investment b (s.bank e w a b).rs (bankInvestment s e w a b) ∧
          BankFOC p e w b (bankInvestment s e w a b) ∧
          (∀ q, OfferOptimal p s.investment e a b ⟨w, 0⟩ .bank q →
            s.investment b q.rs = bankInvestment s e w a b) ∧
          (s.bank e w a b).rs = (s.bank e w 0 b).rs ∧
          bankInvestment s e w a b = bankInvestment s e w 0 b) ∧
        (∀ a, 0 ≤ a → ∀ b ∈ Set.Ico 0 c, ∀ w w',
          wholesaleLower p s c e ≤ w → w ≤ w' →
          (s.bank e w' a b).rs ≤ (s.bank e w a b).rs ∧
          bankInvestment s e w a b ≤ bankInvestment s e w' a b ∧
          offerCash p s.investment e a b ⟨w, 0⟩ .bank (s.bank e w a b) ≤
          offerCash p s.investment e a b ⟨w', 0⟩ .bank (s.bank e w' a b)) := by sorry

end DeepTierFinance.Direct
