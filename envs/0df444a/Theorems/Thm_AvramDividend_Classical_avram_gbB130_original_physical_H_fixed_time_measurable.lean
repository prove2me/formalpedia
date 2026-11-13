-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB130_original_physical_H_fixed_time_measurable
-- name    : AvramDividend.Classical.avram_gbB130_original_physical_H_fixed_time_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:55:54.573136+00:00
-- url     : https://prove2.me/theorems/aff54f56-11d8-4795-872d-6a284f84907a
-- title:
--   Original finite-cap physical stopped postpayment clipped gradient is measurable at every deterministic time
-- statement:
--   At each deterministic nonnegative time s, the original stopped postpayment clipped gradient is measurable with respect to the right-continuous filtration at s. The postpayment reserve is adapted, the stopping indicator is measurable by the stopping-time assumption, and the clipped derivative is Borel measurable because deriv w is continuous on the compact interior band. This extends the proved mesh-time B59 argument to arbitrary physical s, supplying B127 fixed-time integrability.
-- source:
--   Adapted postpayment reserve and stopped clipped derivative measurability, as in proved B59.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_gbB130_original_physical_H_fixed_time_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (s : ℝ≥0) :
    Measurable[𝓕.rightCont s] (fun ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal *
        (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X s ω - rightLimit D s ω
      if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1)
      else 0) := by sorry
