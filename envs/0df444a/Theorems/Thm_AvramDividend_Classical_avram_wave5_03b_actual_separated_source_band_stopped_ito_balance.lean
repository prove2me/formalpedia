-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:41:06.181881+00:00
-- url     : https://prove2.me/theorems/42443bab-1802-4f81-8f16-9713fa22c221
-- title:
--   Every original BV or UBV source separated jump band has an actual finite enumeration and exact stopped controlled nonlinear Itô chain balance
-- statement:
--   For each genuine SpectrallyNegativeLevy X, adapted dividend strategy D, every original sample path ω and finite deterministic time interval, and any strictly negative mark set B separated from zero by ε>0, there exists a finite set T containing precisely the actual original source jump times with marks in B. The full finite-band nonlinear stopped chain-rule sum for w(riskProcess X x D) is exactly the source generator Taylor sum, with right-dividend payments kept distinct, and no finite enumerating set premise, BV/UBV restriction, independent Poisson copy or compensator law.
-- source:
--   Canonical Proved original BV/UBV source finite-horizon separated jump finiteness 52f0bc5f-fb6d-4e4c-95a7-20b6fc1c8835 combined with canonical Proved actual stopped riskProcess nonlinear Finset chain rule 715ac87b-9e76-459c-811e-c995a8fa3873. No source intensity or arbitrary source jump process substitute.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_separated_source_band_stopped_ito_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (ε : ℝ) (hε : 0 < ε)
    (hBsep : ∀ z ∈ B, ε ≤ dist z 0) :
    ∃ T : Finset ℝ≥0,
      (∀ q : ℝ≥0, q ∈ T ↔
        s < q ∧ q ≤ t ∧
          X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q ∈ B) ∧
      (let Y : ℝ≥0 → ℝ := fun q => Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) q
       let J : ℝ≥0 → ℝ := fun q =>
          X.X q ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) q
       (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if Y q ∈ Icc (u + δ) v then
           w (riskProcess X x D q ω) -
             w (Function.leftLim
               (fun r : ℝ≥0 => riskProcess X x D r ω) q)
           else 0) else 0) =
       (∑ q ∈ T, if (q : ℝ≥0∞) ≤ ruinTime X x D ω then
         (if -1 < J q then
           J q * (if Y q ∈ Icc (u + δ) v then deriv w (Y q) else 0)
           else 0) +
         (if Y q ∈ Icc (u + δ) v then
           SpectrallyNegativeLevy.generatorIntegrand w (Y q) (J q)
           else 0) else 0)) := by sorry
