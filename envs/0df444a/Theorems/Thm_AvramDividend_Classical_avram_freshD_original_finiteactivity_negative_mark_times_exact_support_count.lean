-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finiteactivity_negative_mark_times_exact_support_count
-- name    : AvramDividend.Classical.avram_freshD_original_finiteactivity_negative_mark_times_exact_support_count
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T14:41:41.177852+00:00
-- url     : https://prove2.me/theorems/b1e5728b-dd2b-4b1f-8e7c-3a5b9bedec1b
-- title:
--   Original finite-activity negative Lévy jump times admit an exact pathwise finite chronology whose card equals the true intrinsic marked count
-- statement:
--   For the unchanged original spectrally negative Lévy X with finite total strictly negative mark intensity, the actual set of strictly negative physical jump times on (0,T] is finite almost surely. Choose its honest pathwise Finset on this event, and the empty set off that conull event. Proved original Borel finite physical jump-time support c6cc76c9 shows the chosen Finset enumerates exactly all genuinely negative original jumps at almost every omega. Proved exact original Borel marked-count versus finite chronological support-card formula 11e24cb0 (not a substitute Poisson random source) then identifies the cardinal with the exact real-valued intrinsic physical negative jump count on (0,T]. This supplies a concrete finite original S and its actual count needed for chronological nonlinear jump error expectations, without assuming an arbitrary finite support, a synthetic martingale, or globally bounded jump marks. No local Lean compiler runs.
-- source:
--   Avram mixed physical Gaussian plus nonlinear fullnegative marked Itô source 242ca5f1, finite marked physical chronology needed to instantiate newly Proved 71e1a06f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_physical_marked_times_finite_ae
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_Borel_cell_count_equals_marked_support_filter_card_20261116
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_finiteactivity_negative_mark_times_exact_support_count
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) :
    ∃ S : Ω → Finset ℝ≥0,
      ∀ᵐ ω ∂P,
        (∀ u : ℝ≥0, u ∈ S ω ↔
          0 < u ∧ u ≤ T ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u < 0) ∧
        ((S ω).card : ℝ) =
          (((Measure.count.restrict {u : ℝ≥0 |
             0 < u ∧ X.X u ω -
               Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 =>
                (u, X.X u ω -
                  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
              (Ioc 0 T ×ˢ Iio (0 : ℝ))).toReal := by sorry
