-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_negative_Borel_factorial_count_compensator_recurrence_20261115
-- name    : AvramDividend.Classical.avram_a25_original_negative_Borel_factorial_count_compensator_recurrence_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:20:31.796961+00:00
-- url     : https://prove2.me/theorems/05154049-d096-477f-b492-b273fd4233b9
-- title:
--   Original physical negative Borel count factorial-moment compensator recurrence
-- statement:
--   For the actual negative Borel-mark jump count K on the source Lévy process and original probability measure, the (n+1)-st descending factorial count moment equals T ν(B) times the n-th factorial moment. Prove using chronological marked point compensation, newest jump insertion and source predictable count weights. This isolates the genuinely stochastic induction step; normalisation and all-orders moment identities then follow by a simple induction. No independent Poisson companion or changed probability space.
-- source:
--   Original finite marked point count compensator, chronological factorial moment recurrence. Supported initial cases: Proved 4faa7c77 and 6d1258a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_negative_Borel_factorial_count_compensator_recurrence_20261115
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∀ n : ℕ,
      (∫ ω, (Nat.descFactorial (K ω) (n + 1) : ℝ) ∂P) =
        (r : ℝ) * (∫ ω, (Nat.descFactorial (K ω) n : ℝ) ∂P) := by sorry
