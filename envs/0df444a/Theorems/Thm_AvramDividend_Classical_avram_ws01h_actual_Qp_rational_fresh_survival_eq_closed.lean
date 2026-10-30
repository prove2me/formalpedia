-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
-- name    : AvramDividend.Classical.avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T15:18:30.323883+00:00
-- url     : https://prove2.me/theorems/4b5e9dc8-d9cb-43ce-b15d-4a13fd41bef5
-- title:
--   True terminal Esscher Qp rational-grid fresh Lévy survival reward equals genuine full closed-history lower-survival mass
-- statement:
--   Under the genuine random-terminal Esscher measure Qp on the original spectrally negative Lévy path and its independent real Exp(p) observation clock, the nonnegative mass of the countable rational-grid open-horizon survival reward from any reserve x equals exactly the mass of original closed-horizon full continuous lower-survival. This is the required fresh future C_p(x) factor in the genuine stopped first-record Qp regeneration. It derives rational-grid ⇔ weak lower passage pointwise and then uses canonically proved Qp strict/weak lower-clock tie-null integration and strict/closed lower-survival integration. It imports no two-sided exit ratio and does not assume an uncountable variable-path evaluation is jointly measurable.
-- source:
--   Proved WS01H rational_grid ⇔ weak downclock a4d8cdc1, actual Qp strict/weak lower killed integration 1fdee30d, true Qp strict/closed full-history equality 7f51c5a4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_rational_open_survival_iff_weak_lower_clock
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_strict_weak_lower_killing_integral_eq
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_true_Qp_strict_lower_killing_eq_closed_survival_reward

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01h_actual_Qp_rational_fresh_survival_eq_closed
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ p : ℝ) (hθ : 0 ≤ θ) (hp : 0 < p) (x : ℝ) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ n : ℕ, 0 < n → ∀ k : ℕ,
         (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < Real.toNNReal z.2 →
           0 ≤ x + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) z.1}).indicator
         (fun _ => (1 : ℝ≥0∞)) z ∂Qp) =
     (∫⁻ z : Ω × ℝ,
       ({z : Ω × ℝ | 0 ≤ z.2 ∧ ∀ s : ℝ≥0,
         s ≤ Real.toNNReal z.2 →
           0 ≤ x + X.X s z.1}).indicator
         (fun _ => (1 : ℝ≥0∞)) z ∂Qp)) := by sorry
