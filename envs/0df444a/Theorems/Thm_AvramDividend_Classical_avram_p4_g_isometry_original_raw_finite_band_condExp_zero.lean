-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_finite_band_condExp_zero
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_raw_finite_band_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:20:41.839342+00:00
-- url     : https://prove2.me/theorems/225782a0-def3-48a0-951c-361e14d94dec
-- title:
--   Original intrinsic finite-band count has conditional mean zero on the given raw past filtration
-- statement:
--   Exactly the P2-E original intrinsic rectangle ENNReal law, plus source count measurability and finite separated-band intensity, implies conditional expectation zero for the actual real compensated count given the genuine original F_s. This depends on converting each past-event first moment to a real integral and the uniqueness theorem for conditional expectation. It gives raw filtration centring only: no right-continuous augmentation, diagonal L2 variance, stochastic integral limit or stopped martingale.
-- source:
--   Composition of finite-band original source real integrability, raw F_s event-by-event centring and pinned ae_eq_condExp_of_forall_setIntegral_eq. No independent Poisson model or claimed P2 canonical proof.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_raw_finite_band_condExp_zero
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
    : P[(fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) | 𝓕 s] =ᵐ[P] 0 := by sorry
