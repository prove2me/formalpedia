-- Prove2me | Theorems.Thm_DSDensity1246_Main_Supplement_optimal_realizable_list_learning
-- name    : DSDensity1246.Main.Supplement.optimal_realizable_list_learning
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-11-15T06:25:43.117255+00:00
-- url     : https://prove2.me/theorems/867549fc-d522-402a-9b24-fdf3988b6a1e
-- title:
--   Theorem 3 — Optimal Sample Complexity for List Learning
-- statement:
--   Let H⊆Yˣ be any hypothesis class with finite scale-ℓ DS dimension d, where ℓ≥1. There is a randomized ℓ-list learner A, chosen independently of the data distribution, such that for every H-realizable probability distribution D and every 0<ε,δ<1,
--
--   $$m\ge\left\lceil\frac{512(d+\log(1/\delta))}{\varepsilon}\right\rceil
--   \quad\Longrightarrow\quad
--   \Pr_{S\sim D^m,r}\!\left[\operatorname{err}_D(A(S,r))>\varepsilon\right]\le\delta.$$
--
--   The constant is universal, independent of ℓ,X,Y,H and D. When d=0, the same conclusion holds for every m≥0 using the label-union rule. For d≥1 the learner is the explicitly defined randomized prefix-validation construction from one-inclusion predictors. Realizability means infimum error zero rather than an attained error-zero target. Every output list has size at most ℓ, and failure probability includes both sampling and internal randomness.
--
--   This is the companion upper learning theorem; it is not used to prove the published density goal.
--
--   Differences from the source:
--   - encoding: probabilities over iid data and independent internal randomness, with realizability defined by an error infimum of zero → unbundled Mathlib probability laws carrying their own σ-algebras on arbitrary labeled data spaces, finite product sampling with an independent seed law, outer probabilities of arbitrary events, and an ENNReal single-hypothesis infimum; reason: no countability, finite-support, measurability, or attainment restriction is introduced; measurable cases agree with ordinary probability and the empty-class infimum is infinity
--   - encoding: m = O((d + log(1/δ))/ε) → the sufficient budget ceil(512(d+log(1/δ))/ε), with zero samples allowed when d=0; reason: pp.19–20 give 4.82 and exp(−vε/12); the displayed n,R,v choices total at most 256(d+log(1/δ))/ε for d≥1, and dimension zero permits the label-union rule
--   - encoding: there exists a randomized list learner from one-inclusion predictors, sampled prefixes and validation → existential orientation choices in the explicit validatedLearner, with an independent uniform seed on [0,1) and conventional accuracy/confidence inputs; reason: the seed produces the same independent finite prefix choices; the rule is fixed before the data distribution, uses no target, and ignores surplus observations
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 19, Theorem 3; proof pp. 19-20

import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_Supplement_predictor

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- Theorem 3, pp.19–20: a distribution-independent randomized learner.
The explicit constant 512 follows from the proof's 4.82 and validation constants.
Accuracy and confidence range over their full open unit intervals; d=0 needs no data.
The orientation choices and the uniform seed law are conclusions, not assumptions. -/
theorem optimal_realizable_list_learning {X Y : Type*}
    (H : Set (X → Y)) (ℓ d : ℕ) (hℓ : 1 ≤ ℓ) (hd : listDSDim ℓ H = d) :
    ∃ (C : OrientationChoice X Y ℓ H) (ρ : ProbabilityMeasure ℝ),
      (ρ : Measure ℝ) = volume.restrict (Set.Ico (0 : ℝ) 1) ∧
      ∀ (D : DataLaw (X × Y)), Realizable D H →
        ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
          ∀ m : ℕ,
            (if d = 0 then 0 else ⌈512 * ((d : ℝ) + Real.log (1 / δ)) / ε⌉₊) ≤ m →
            failureProbability D ρ (validatedLearner d C) ε δ m 0 ≤ ENNReal.ofReal δ := by sorry

end DSDensity1246.Main.Supplement
