-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:09:31.982116+00:00
-- url     : https://prove2.me/theorems/ba8f57d7-efd2-4214-934f-2db5018f5a0f
-- title:
--   Original intrinsic separated negative-band count is L1 under source rectangle compensation
-- statement:
--   On the original sample space and original source filtration, the intrinsic Lévy jump count in a strictly negative band separated from zero is almost surely finite and its real-valued count integrable, assuming precisely the P2-E past-event rectangle ENNReal expectation identity, actual count identity, measurability and finite Lévy intensity. This proves first-moment integrability only; no second moments, predictable variance, right-continuity extension or stopped martingale is asserted.
-- source:
--   P2-E original intrinsic count rectangle law at A=univ, X.isProbability, pinned integrable_toReal_of_lintegral_ne_top and ae_lt_top, ENNReal.mul_lt_top.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
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
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Integrable (fun ω => (N ω).toReal) P ∧
      (∀ᵐ ω ∂P, N ω < ⊤) := by sorry
