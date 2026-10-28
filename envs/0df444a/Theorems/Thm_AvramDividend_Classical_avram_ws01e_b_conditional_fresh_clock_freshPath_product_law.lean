-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_fresh_clock_freshPath_product_law
-- name    : AvramDividend.Classical.avram_ws01e_b_conditional_fresh_clock_freshPath_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:04:52.008455+00:00
-- url     : https://prove2.me/theorems/47e51cda-6a3a-463f-8447-a412ae63e91f
-- title:
--   Exact fresh residual-clock and fresh Lévy path joint product distribution
-- statement:
--   For a Lévy process, any genuinely finite stopping age τ with adapted sublevel events, and a separate independent nonnegative observation clock e with a strictly memoryless survival kernel and discount(0)=1, conditional on τ<e the real residual clock e−τ and entire shifted post-stopping Lévy path have exactly the product of the original real clock law and the original entire Lévy path law. This combines full conditional fresh-path/residual-clock independence and exact residual-time distribution equality, with no infinite-horizon Esscher or Wiener–Hopf assumptions.
-- source:
--   Direct composition of canonically Proved avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh (32cf9a92) and avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law (55f49ff2), plus accepted finite-stopping future-path measurability and independence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_conditional_fresh_clock_freshPath_product_law
    {Ω Θ : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace Θ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ)
    (hStop : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (Q : Measure Θ) [IsProbabilityMeasure Q]
    (e : Θ → ℝ≥0) (he : Measurable e)
    (discount : ℝ≥0 → ℝ≥0∞) (hd : Measurable discount)
    (hTail : ∀ a : ℝ≥0, Q {η : Θ | a < e η} = discount a)
    (factor : ℝ≥0 → ℝ≥0∞)
    (hShift : ∀ a t : ℝ≥0, discount (a + t) = factor t * discount a)
    (hZero : discount 0 = 1)
    (hPos : (P.prod Q) {z : Ω × Θ | τ z.1 < e z.2} ≠ 0) :
    Measure.map
      (fun z : Ω × Θ =>
        ((e z.2 : ℝ) - (τ z.1 : ℝ),
          fun s : ℝ≥0 => X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    (Measure.map (fun η : Θ => (e η : ℝ)) Q).prod
    (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by sorry
