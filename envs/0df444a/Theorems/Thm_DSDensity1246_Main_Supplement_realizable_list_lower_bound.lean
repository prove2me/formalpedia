-- Prove2me | Theorems.Thm_DSDensity1246_Main_Supplement_realizable_list_lower_bound
-- name    : DSDensity1246.Main.Supplement.realizable_list_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T06:26:17.749647+00:00
-- url     : https://prove2.me/theorems/fd530287-6e57-487e-b7a8-d977450df8ff
-- title:
--   Theorem 5 — Realizable List Learning Lower Bound
-- statement:
--   Let H⊆Yˣ have scale-ℓ DS dimension d≥2, where ℓ≥1. Suppose H also (2ℓ−1)-DS shatters a sequence of length d. For every randomized ℓ-list learner A with any independent seed law, every 0<ε,δ<1/16, and every natural sample size m satisfying
--
--   $$m\le\frac{d+\log(1/\delta)}{128\varepsilon},$$
--
--   there is an H-realizable distribution D such that
--
--   $$\Pr_{S\sim D^m,r}\!\left[\operatorname{err}_D(A(S,r))>\varepsilon\right]>\delta.$$
--
--   The distribution may depend on the learner, parameters and sample size. Both dimension and confidence terms remain in the bound. The additional shattering premise is the full published DS-neighbor condition, not a Cartesian-box assumption.
--
--   This companion result establishes the realizable lower rate under the paper's label-richness hypothesis.
--
--   Differences from the source:
--   - encoding: probabilities over iid data and independent internal randomness, with realizability defined by an error infimum of zero → Mathlib probability measures on arbitrary labeled data spaces, finite product sampling with an independent seed law, outer probabilities of arbitrary events, and an ENNReal single-hypothesis infimum; reason: no countability, finite-support, measurability, or attainment restriction is introduced; measurable cases agree with ordinary probability and the empty-class infimum is infinity
--   - encoding: m = Ω((d + log(1/δ))/ε) → every natural m ≤ (d+log(1/δ))/(128ε) admits a realizable distribution with strict failure probability greater than δ; reason: pp.21–23 give obstructions at d/(64ε) and log(1/δ)/(64ε); at least one holds under the stated sum threshold
--   - encoding: the proof constructs finitely supported hard distributions → the existential hard data law is required to carry the all-sets σ-algebra; reason: the source finite atomic witnesses are defined on every subset, so data errors are genuine measurable probabilities; arbitrary learner seed spaces and all source instances remain covered
-- source:
--   Chirag Pabbaraju, STOC 2027 submission #1246 (October 2026), p. 20, Theorem 5; proof pp. 20-23

import Definitions.Def_DSDensity1246_Main_dsModel
import Definitions.Def_DSDensity1246_Main_Supplement_learning

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace DSDensity1246.Main.Supplement

/-- Theorem 5, pp.20–23: both lower-bound terms, with the source's stronger
shattering assumption. The constant 1/128 combines the two proof obstructions. -/
theorem realizable_list_lower_bound {X Y R : Type*}
    [MeasurableSpace R]
    (H : Set (X → Y)) (ℓ d : ℕ) (hℓ : 1 ≤ ℓ) (hd₂ : 2 ≤ d)
    (hd : listDSDim ℓ H = d)
    (hrich : ∃ S : Fin d → X, ListDSShatters (2 * ℓ - 1) H S)
    (ρ : ProbabilityMeasure R) (A : ListLearner X Y R ℓ)
    (ε δ : ℝ) (hε : 0 < ε) (hε₁ : ε < 1 / 16)
    (hδ : 0 < δ) (hδ₁ : δ < 1 / 16) (m : ℕ)
    (hm : (m : ℝ) ≤ ((d : ℝ) + Real.log (1 / δ)) / (128 * ε)) :
    ∃ D : DataLaw (X × Y), D.1 = ⊤ ∧ Realizable D H ∧
      ENNReal.ofReal δ < failureProbability D ρ A ε δ m 0 := by sorry

end DSDensity1246.Main.Supplement
