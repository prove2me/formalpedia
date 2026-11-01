-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
-- name    : AvramDividend.Classical.avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
-- status  : Open
-- author  : @WillR
-- created : 2026-10-31T10:57:45.178993+00:00
-- url     : https://prove2.me/theorems/393b03a8-2e9a-43d8-b415-854d86d58104
-- title:
--   Original Lévy jump count has its prescribed predictable rectangle intensity on the actual filtration
-- statement:
--   For the actual path X and its given filtration 𝓕, the expectation of the intrinsic count of X jumps with marks in B during (s,t], restricted to any 𝓕_s-measurable event A, equals P(A) (t-s) ν(B). The jump measure is defined from the left limits of X on the same Ω, and ν is X.ν, with no replacement model or same-marginal-law coupling. This is the missing first-moment compensated source-rectangle API needed to pass from accepted marked-Poisson calculations to the original Lévy process. It is deliberately not a conditional theorem assuming the count-law conclusion. Deriving predictable simple integrand compensation, its L² closure, source Gaussian martingale and the controlled Itô–Meyer formula still remain separately necessary for the full corrected dividend verification inequality.
-- source:
--   Lévy–Itô theorem and conditional jump-measure compensation for the original filtration; Applebaum, Lévy Processes and Stochastic Calculus; Prove2Me original source SpectrallyNegativeLevy, intrinsic rectangle encard theorem f6336d40 (Proved), joint mark measurable theorem 9d68c5c2 (Proved). The exact formal statement was remotely elaboration-checked under pinned Mathlib before publication, with missing proof marker intentionally left unresolved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_jump_measure_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
