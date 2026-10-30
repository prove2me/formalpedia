-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_finite_clock_killed_mass_squeeze
-- name    : AvramDividend.Classical.avram_ws01h_true_Qp_finite_clock_killed_mass_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:39:05.759728+00:00
-- url     : https://prove2.me/theorems/ec0923fc-bbce-4799-87c5-58471f2c07b8
-- title:
--   True lower-killed finite Esscher Qp first-record renewal mass squeezed within the exact no-record exponential CDF error
-- statement:
--   Under the genuine original spectrally negative Lévy process and its actual finite-rate terminal Esscher Qp, the full closed lower-survival mass up to a finite observation cap is bounded below by the actual lower-killed first-record fresh-future survival mass and above by that same killed-record mass plus the true Exp(lambda) CDF at upper-gap b. This uses the canonically proved exact disjoint genuine finite-clock source-partition, the canonically proved weak (not merely strict) Qp no-record supremum bound, and the genuine shifted-root hypothesis. No two-sided exit scale ratio or artificial full-path Esscher law is assumed. This is the quantitative finite-clock CDF renewal remainder bound.
-- source:
--   Proved source-specific mass partition 454f0ad4, proved Qp weak no-record exponential CDF bound f98ad01c, positive-root shifted Esscher law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_genuine_finite_clock_killed_record_mass_partition
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_true_Qp_finite_clock_killed_mass_squeeze
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (x b : ℝ) (hb : 0 ≤ b) (N : ℝ≥0) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * q)))
     let τ : Ω → ℝ≥0 := fun ω =>
       (min (twoSidedExitUpTime X b ω) (N : ℝ≥0∞)).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       Real.toNNReal z.2 ≤ N ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - τ z.1 →
         0 ≤ (x + b) + (X.X (τ z.1 + u) z.1 - X.X (τ z.1) z.1)}
     Qp A ≤ Qp E ∧
       Qp E ≤ Qp A + (expMeasure lam) (Iic b)) := by sorry
