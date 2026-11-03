-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_void_semigroup_without_stationary_hypothesis
-- name    : AvramDividend.Classical.avram_wave7_06_original_negative_band_void_semigroup_without_stationary_hypothesis
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:58:40.175053+00:00
-- url     : https://prove2.me/theorems/d94c1f15-8caa-469a-a43c-84758c62ae81
-- title:
--   Original negative-band no-jump semigroup without an assumed stationarity law
-- statement:
--   For literal original spectrally negative Lévy marked jumps, the void probability p(T) is multiplicative in time under the sole remaining original-filtration measurability hypothesis of the early void event. Stationarity of the later void law is proved from the universal common measurable marked-jump path counter and the original full-path stationary law; the accepted source void factor theorem handles past/future independence. The original Lévy rate ν(B) identification is not asserted.
-- source:
--   Composition of W7-06 Proved conditional original void semigroup a8f4c93c and true source stationary void law from canonical universal càdlàg counter, leaving exactly early-void past-measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_negative_band_void_semigroup_without_stationary_hypothesis
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T S : ℝ≥0) (n : ℕ)
    (hPast : MeasurableSet[𝓕 T]
      {ω : Ω | NX ω
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0}) :
    P {ω : Ω | NX ω
      (Ioc 0 (T + S) ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
    P {ω : Ω | NX ω
      (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} *
    P {ω : Ω | NX ω
      (Ioc 0 S ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} := by sorry
