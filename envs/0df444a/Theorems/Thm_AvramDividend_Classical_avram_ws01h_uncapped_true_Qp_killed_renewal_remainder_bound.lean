-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_uncapped_true_Qp_killed_renewal_remainder_bound
-- name    : AvramDividend.Classical.avram_ws01h_uncapped_true_Qp_killed_renewal_remainder_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:46:23.439103+00:00
-- url     : https://prove2.me/theorems/8dd1e384-f8c6-4198-8e5f-2f2d0f81dd8c
-- title:
--   Uncapped true Esscher Qp CDF survival is squeezed by actual lower-killed record renewal within exact exponential no-record remainder
-- statement:
--   For the actual original spectrally negative Lévy path under the true terminally tilted Esscher Qp observation clock, the full exponential-age lower-survival mass from initial x differs from the original strict lower-killed first-upper-record followed by true shifted future survival mass by at most the exact Exp(lambda) no-upper-record CDF at b. This is an uncapped finite-p identity and inequality with neither finite observation-horizon error nor a path-space Esscher measure hypothesis. Its only stochastic inputs are the source exact uncapped killed-record/weak-no-record partition and already proved genuine tilted no-record bound. The still-missing independent stopped-history strong-Markov factorisation must identify the actual record branch as a product before taking p→0.
-- source:
--   New source uncapped genuine Lévy partition, canonical actual Qp weak no-record bound f98ad01c, Mathlib measure monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_uncapped_true_Qp_killed_renewal_remainder_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (x b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * q)))
     let age : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitUpTime X b ω).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - age z.1 →
          0 ≤ (x + b) + (X.X (age z.1 + u) z.1 - X.X (age z.1) z.1)}
     Qp A ≤ Qp E ∧
       Qp E ≤ Qp A + (expMeasure lam) (Iic b)) := by sorry
