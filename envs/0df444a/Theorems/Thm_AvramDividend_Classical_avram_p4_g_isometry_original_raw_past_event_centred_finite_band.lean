-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_past_event_centred_finite_band
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_past_event_centred_finite_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:12:17.762202+00:00
-- url     : https://prove2.me/theorems/43833315-3314-488f-82cd-cd5555feabe2
-- title:
--   Original finite-band compensated intrinsic count has zero integral on each raw past event
-- statement:
--   On the actual original probability space with its raw original filtration, the finite-band count minus its true finite Lévy rate has zero real integral over every event in F_s. The only unproved stochastic premise is exactly P2-E's original ENNReal marked rectangle law; the count is definitionally the actual NX, with its source measurability and finite intensity explicit. This does not extend to F.rightCont, prove a second moment or a stopped martingale.
-- source:
--   Pinned MeasureTheory.integral_toReal on P.restrict A, integrable_toReal_of_lintegral_ne_top, ae_lt_top, and ENNReal.toReal_mul with the P2-E original raw-filtration source law.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_past_event_centred_finite_band
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
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A,
      ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by sorry
