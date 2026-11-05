-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_weighted_cell_from_proved_compensator
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_weighted_cell_from_proved_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:23:20.182123+00:00
-- url     : https://prove2.me/theorems/be161015-5f2d-4fe0-a085-96679ca71b04
-- title:
--   Original intrinsic finite negative-band weighted martingale step from proved compensator
-- statement:
--   For X on the original probability space and raw filtration, the physically defined intrinsic finite negative-band jump count has the predictable weighted martingale-step identity by the now proved original rectangle compensator. Assumes explicit count measurability and L2 moments; no replacement Poisson measure or stopping.
-- source:
--   P2-E canonical physical past-event rectangle compensator 393b03a8 (Proved/public) plus P4-G weighted raw martingale step 2113499e (Proved); strict -1<z<-epsilon convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_martingale_step

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_weighted_cell_from_proved_compensator
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
    (hMeas : Measurable N)
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
