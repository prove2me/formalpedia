-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_genuine_tilted_exponential_stopped_freshPair_regeneration
-- name    : AvramDividend.Classical.avram_ws01e_b_genuine_tilted_exponential_stopped_freshPair_regeneration
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T10:15:29.599403+00:00
-- url     : https://prove2.me/theorems/8d6dcc35-2564-4fcd-a535-f4011b4a7755
-- title:
--   True random-terminal Esscher stopped residual-clock and full shifted-path regeneration
-- statement:
--   Under a genuine spectrally negative Lévy law P and independently exponentially distributed observation time e, define Qp exactly as the path×real-clock product weighted by the likelihood exp(θX_e−eψ(θ)), θ≥0 and p>0. For any finite measurable stopping age τ with the stated filtration stopping condition, and positive Qp survival event τ<e, the conditional Qp pushforward of (e−τ, entire centred shifted post-τ Lévy path) equals the unconditional Qp pushforward of (e, original entire Lévy path). This is genuine regeneration of the joint clock/path pair, which remains coupled through its random-terminal density. In particular it does not assert that under Qp the entire path and clock are independent. Instantiating at capped strict first upper records and removing the cap is a separate obligation.
-- source:
--   Noncircular target combining true original-law full residual-clock/fresh-path product 7ad19b0b and bb341912, exact stopped Esscher likelihood split b2a39955 and first upper-record hit split a1fddcf8, true random-terminal density normalisation 146b0027, and bounded/finite-grid Esscher stopped-prefix factor 8d968653. The new obligation is the stopped-history-weighted product and its normalising survival mass. Publication repair: add the exact Reflection definition import to establish the AvramDividend.Classical namespace and SpectrallyNegativeLevy, and write the conditional measure as ProbabilityTheory.cond Qp event to avoid bracket-notation parser ambiguity.

import Mathlib
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_AvramDividend_Classical_Reflection

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_genuine_tilted_exponential_stopped_freshPair_regeneration
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Qp : Measure (Ω × ℝ))
    (hQp : Qp =
      ((P.prod (expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal
          (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
            (Real.toNNReal z.2 : ℝ) * X.ψ θ)))))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))))
    (hSurvivalMeas : MeasurableSet
      {z : Ω × ℝ | τ z.1 < Real.toNNReal z.2})
    (hSurvivalPos :
      Qp {z : Ω × ℝ | τ z.1 < Real.toNNReal z.2} ≠ 0) :
    Measure.map
      (fun z : Ω × ℝ =>
        ((Real.toNNReal z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 =>
            X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      (ProbabilityTheory.cond Qp {z : Ω × ℝ | τ z.1 < Real.toNNReal z.2}) =
    Measure.map
      (fun z : Ω × ℝ =>
        ((Real.toNNReal z.2 : ℝ),
          fun s : ℝ≥0 => X.X s z.1))
      Qp := by sorry
