-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
-- name    : AvramDividend.Classical.avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:43:50.602915+00:00
-- url     : https://prove2.me/theorems/878da3f9-37bc-4b29-97d7-afb4d0d29743
-- title:
--   The true original finite negative marked Poisson count on any physical interval has exact integrable real first moment
-- statement:
--   For the unchanged original finite-negative-activity spectrally negative Lévy X source on its own probability space and any negative Borel mark band B, the true physical marked Poisson counting measure on any chronological strict-left/inclusive-right interval (s,t] has an integrable real-valued count with EXACT expected value of the finite intensity ((t-s)ν(B)).toReal. This converts the source-sound original negative Borel interval Campbell mean into a usable first-moment L1 bound, without synthetic marked processes, extra independence assumptions or large negative jump moments. It is the quantitative companion required by the original Jsmall physical interval variation bound for stopped Itô-Meyer convergence.
-- source:
--   Proved original physical marked Poisson rectangular count measurability and new exact interval negative Borel Campbell mean.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_negative_Borel_marked_interval_real_count_integrable_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal := by sorry
