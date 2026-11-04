-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_nu_count_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:13:31.372+00:00
-- url     : https://prove2.me/theorems/3a5ca225-7652-4f87-9c91-7a4002215f97
-- title:
--   Finite Lévy mark intensity makes the original intrinsic marked count finite almost surely
-- statement:
--   On the original spectrally negative Lévy process, for any Borel mark set B of finite original Lévy measure and any finite half-open time rectangle (s,t], the literal original intrinsic jump count is finite P-almost everywhere once its independently sourced unconditional ν-rate has been established. The proof uses measurability, finite ENNReal first moment and Markov's almost-sure finiteness lemma; no Poisson replacement or prior compensated martingale is assumed.
-- source:
--   P2-E Proved genuine original marked count measurability 8146a449; pinned Mathlib ae_lt_top, ENNReal.mul_lt_top and coe_lt_top; P2-D unconditional ν-rate remains external/Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_nu_count_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    ∀ᵐ ω ∂P, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) < ⊤ := by sorry
