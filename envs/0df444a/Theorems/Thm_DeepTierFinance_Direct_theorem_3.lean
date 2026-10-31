-- Prove2me | Theorems.Thm_DeepTierFinance_Direct_theorem_3
-- name    : DeepTierFinance.Direct.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T14:27:26.816982+00:00
-- url     : https://prove2.me/theorems/fa15b26d-df75-46b7-bbf7-5987968a0ac5
-- title:
--   Theorem 3 — optimal direct financing and universal adoption
-- statement:
--   For the Section 3 primitives, the source capital construction and response system exist. For every probability distribution on [0,c), there are traditional and delegate equilibria and an optimal direct-finance menu for every profile in W. There is a threshold bar-check-e(θ₂), independent of θ₁ and e and nonincreasing in θ₂, with all of the following properties:
--
--   1. The direct loan rate is nonnegative, depends on θ₂ and the emergency-cost regime, and is at most the traditional tier-1 AP rate r_s*.
--   2. If e>bar-check-e(θ₂), the wholesale price equals the tier-1 participation boundary bar-check-w¹ and is at most w*. Otherwise it equals e, including equality at the threshold. The direct threshold is at most the delegate emergency threshold bar-hat-e(θ₁,θ₂).
--   3. All three agents strictly improve their realized profits, so both suppliers always adopt.
--   4. The implemented investment satisfies check-y*≥y*.
--
--   The direct menu attains the global maximum of (13) over all implemented contracts satisfying (14). Neither existence nor adoption is assumed, and neither is replaced by a supremum, a limiting price, or weak participation. The printed boundary/strict-participation conflict is deliberately retained.
--
--   Differences from the source:
--   - encoding: named derived optimal responses and capital bounds → existential response data with cash-flow and optimality certification in the conclusion; reason: existence and positivity asserted by the source are not assumed of the primitives, and there are no default argmax selections
--   - encoding: an arbitrary distribution F on [0,c) → a Borel probability measure with mass one on [0,c) and integrable response-induced payoffs; reason: this implements the stated expectation without a density or finite-support restriction or a default nonintegrable integral
--   - encoding: terminal cash in (2)–(3) and profits in participation constraints → initial capital is subtracted from supplier cash in every adoption comparison; reason: this compares the same profit convention on both sides
--   - reading: joint bank/manufacturer financing is allowed and AP is deducted in settlement before bank repayment → mixed-loan deviations use invoice netting of AP before capped residual bank repayment; reason: the timing on pp. 8–9 supplies this priority convention; both pure financing cases reduce exactly to (2)–(3)
--   - encoding: an infinity-valued manufacturer AP rate denotes BF → Option.none denotes no manufacturer-finance offer and forces zero manufacturer principal; reason: no infinite-rate arithmetic or artificial large finite rate is introduced
--   - reading: increases and decreases without a strict inequality → nondecreasing and nonincreasing comparisons; reason: the source separately writes strict inequalities where intended and the emergency branch caps investment incentives
--   - reading: Bs and Bm in Table 3 failure rows → both denote the direct advance (y-theta2)^+; reason: the caption defines this single loan; subtracting tier-1 capital would describe delegate financing instead
--   - encoding: bar-check-w1 is the tier-1 participation boundary → the boundary is expressed by P(y)(w-v)=pi1_old; reason: the equality remains distinct from strict feasibility and avoids division by a possibly zero probability
-- source:
--   Dong, Qiu and Xu (2022), Blockchain-Enabled Deep-Tier Supply Chain Finance, MSOM forthcoming, supplied May 2022 manuscript, DOI 10.1287/msom.2022.1123 (published citation basis), Theorem 3, printed p. 23, PDF p. 23

import Definitions.Def_DeepTierFinance_Direct_Characterizations
open DeepTierFinance.Direct

namespace DeepTierFinance.Direct

theorem theorem_3 (p : Primitives) (hp : p.Valid) :
    ∃ c R, CoreValid p c R ∧ ∀ μ : MeasureTheory.Measure ℝ, Prior μ c →
      ∃ (T : TraditionalPolicy) (D : DelegatePolicy) (direct : DirectPolicy) (rate : ℝ → ℝ → ℝ) (tDirect : ℝ → ℝ) (tDelegate : ℝ → ℝ → ℝ),
        TraditionalEquilibrium p c μ R T ∧ DelegateEquilibrium p c R T D ∧
        AntitoneOn tDirect (Set.Ico 0 c) ∧
        (∀ a b, DelegateEmergencyThreshold p c R T D a b (tDelegate a b)) ∧
        ∀ e, EmergencyCost p e → ∀ a b, CapitalRegion p (R e) c e a b →
          let m := direct e a b
          let y := (R e).investment b m.r
          let old := T.response e a b (T.menu e a)
          DirectOptimal p (R e) T e a b m ∧
          m.r = rate e b ∧ m.r ≤ old.offer.rs ∧
          (if tDirect b < e then
            DirectParticipationBoundary p T e a b y m.w ∧ m.w ≤ (T.menu e a).w ∧ m.w < e
           else m.w = e) ∧
          tDirect b ≤ tDelegate a b ∧
          realizedBenchmark p T e a b 0 < directProfits p e b m y 0 ∧
          realizedBenchmark p T e a b 1 < directProfits p e b m y 1 ∧
          realizedBenchmark p T e a b 2 < directProfits p e b m y 2 ∧
          old.y ≤ y := by sorry

end DeepTierFinance.Direct
