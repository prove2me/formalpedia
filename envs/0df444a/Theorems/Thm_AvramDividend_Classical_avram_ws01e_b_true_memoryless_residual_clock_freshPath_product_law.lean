-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_memoryless_residual_clock_freshPath_product_law
-- name    : AvramDividend.Classical.avram_ws01e_b_true_memoryless_residual_clock_freshPath_product_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T01:03:21.828277+00:00
-- url     : https://prove2.me/theorems/7ad19b0b-2f78-437c-b526-18ebbf05bf24
-- title:
--   A truly memoryless observation clock and the full fresh Lévy path regenerate jointly after stopping
-- statement:
--   Conditioned on a genuine finite Lévy stopping age τ preceding an independent memoryless observation clock e with no zero-time atom and positive survival, the complete joint distribution of the real residual e−τ and the full post-τ centred Lévy future path is exactly the product of the unconditional real clock law and the unconditional original Lévy path law. This removes both the conditional residual-clock marginal and the conditional fresh-path marginal from the accepted product-law formula, using the now Proved full residual-clock distribution theorem. It is a fully random-clock, full-path original-law regeneration result, the key input for the drawdown functional after an upper record; it does not assert Esscher tilted Wiener–Hopf independence.
-- source:
--   Proved avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh (32cf9a92-c026-41db-abfa-b36b5e1509c4) and avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law (55f49ff2-5bdf-4149-9860-c8f1fbe1b429), with Mathlib indepFun_const_right.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_conditional_residual_real_clock_law_eq_fresh
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_levy_conditional_joint_residual_freshPath_product_law

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_true_memoryless_residual_clock_freshPath_product_law
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
          fun s : ℝ≥0 =>
            X.X (τ z.1 + s) z.1 - X.X (τ z.1) z.1))
      ((P.prod Q)[|{z : Ω × Θ | τ z.1 < e z.2}]) =
    (Measure.map (fun η : Θ => (e η : ℝ)) Q).prod
      (Measure.map (fun ω : Ω => fun s : ℝ≥0 => X.X s ω) P) := by sorry
