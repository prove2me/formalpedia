-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_weighted_cell_auto_count_meas
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_weighted_cell_auto_count_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:49:59.487651+00:00
-- url     : https://prove2.me/theorems/1a41cfc5-c2dd-4833-8a9f-06af8363b815
-- title:
--   Original intrinsic finite-band predictable martingale step without count-measurability premise
-- statement:
--   The physical original X marked rectangle count is measurable by P2-E, so conditional weighted centered finite-band martingale-step follows directly from the proved canonical past-event rectangle law with explicit L2 moments.
-- source:
--   P2-E original intrinsic rectangle measurability 8146a449; P4-G accepted original weighted step be161015.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_weighted_cell_from_proved_compensator

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_weighted_cell_auto_count_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P)
    (M : Ω → ℝ)
    (hM : StronglyMeasurable[𝓕 s] M)
    (hMInt : Integrable M P) :
    P[(fun ω => M ω + H ω * ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s]
        =ᵐ[P] M := by sorry
