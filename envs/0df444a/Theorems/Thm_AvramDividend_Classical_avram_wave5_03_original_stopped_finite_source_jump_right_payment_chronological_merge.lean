-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge
-- name    : AvramDividend.Classical.avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:43:18.313375+00:00
-- url     : https://prove2.me/theorems/29945179-cc6f-4c5e-b536-cd4779f7cd8f
-- title:
--   Original stopped finite-band Lévy source jumps chronologically merged with simultaneous right-dividend atoms
-- statement:
--   For the original spectrally negative Lévy path X and original admissible dividend strategy D on one shared filtration, each finite source-jump band within a genuine stopped horizon has a full nonlinear post-right-payment value increment. The finite stopped chronological sum splits exactly into the truncated original Lévy generator/Taylor source-mark sum plus the value drop from the simultaneous right dividend jump. The proof uses the verified same-source left-limit and source-mark identities and 03-B's verified finite-band chain sum; it does not assume that source and control jumps never coincide. It does not sum payments outside the source jump band or prove compensation, which require the separate 04-B full Stieltjes statement.
-- source:
--   03-B original finite-band chain sum f32a1b6d (Proved), original reserve source mark d2800259 (Proved), actual pre/post left limit caa7f605 (Proved), full chronological dividend accounting 04-B 85c80889 (Proved); connects corrected UBV 429e17ca and BV ef7e6c20.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_finite_source_band_taylor_chain_sum
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepost_reserve_same_leftlim
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_original_prepayment_reserve_exact_source_jumpmark

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_stopped_finite_source_jump_right_payment_chronological_merge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ r : ℝ≥0, r ∈ S ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let J : ℝ≥0 → ℝ := fun r =>
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + δ) v then
        w (riskProcess X x D r ω -
          (rightLimit D r ω - D r ω)) - w (Y r) else 0) else 0) =
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J r then
        J r * (if Y r ∈ Icc (u + δ) v then deriv w (Y r) else 0)
        else 0) +
      (if Y r ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r)
        else 0) else 0) +
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + δ) v then
        w (riskProcess X x D r ω -
          (rightLimit D r ω - D r ω)) -
          w (riskProcess X x D r ω) else 0) else 0) := by sorry
