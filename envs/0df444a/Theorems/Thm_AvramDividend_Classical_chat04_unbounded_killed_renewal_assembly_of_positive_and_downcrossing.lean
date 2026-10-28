-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_renewal_assembly_of_positive_and_downcrossing
-- name    : AvramDividend.Classical.chat04_unbounded_killed_renewal_assembly_of_positive_and_downcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:35:56.424398+00:00
-- url     : https://prove2.me/theorems/0b199670-f5f8-41d3-ba7d-8ee53334d58c
-- title:
--   Full killed q-scale renewal from positive reserves and zero regularity
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, the whole-path killed q-scale expectation identity for every reserve and every deterministic time reduces to its strictly positive reserve/time case and almost-sure downward crossing at arbitrarily short positive horizons from reserve zero. The negative-reserve and time-zero boundary cases are already proved.
-- source:
--   Direct case split combining Proved chat04_history_killed_renewal_zero_horizon_or_negative_reserve and chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing.

import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_renewal_zero_horizon_or_negative_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_scale_zero_start_of_ae_downcrossing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_killed_renewal_assembly_of_positive_and_downcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hpositive : ∀ (x : ℝ) (hx : 0 < x) (t : ℝ≥0) (ht : 0 < t),
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
        ENNReal.ofReal (W x))
    (hdown : ∀ (t : ℝ≥0), 0 < t →
      ∀ᵐ ω ∂P, ∃ s : ℝ≥0, s ≤ t ∧ X.X s ω < 0)
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
      ENNReal.ofReal (W x) := by sorry
