-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn39_original_finite_right_atoms_plus_signed_source_mean
-- name    : AvramDividend.Classical.avram_bv_env3_turn39_original_finite_right_atoms_plus_signed_source_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:48:51.954473+00:00
-- url     : https://prove2.me/theorems/7a4c1b1a-02a4-4a2c-b751-2152519099dc
-- title:
--   Original signed BV martingale-drift source plus all finitely marked zero/pre-ruin dividend atoms
-- statement:
--   For the actual original dividend riskProcess, add the discounted physical signed atom residuals of any finite collection of right-limit dividend times including the time-zero atom to an integrable nonpositive-mean source process. Assuming only explicit L1 integrability of the marked atom sum, the resulting full original finite-mark signed source is integrable with nonpositive mean. This isolates the finite-atom case of original stopped Ito and leaves only physical mesh limits and endpoint accounting.
-- source:
--   BV-ENV3 original stopped C1 signed physical atom reduction, for combining accepted original compensated source budget with full finite tagged cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn39_original_finite_right_atoms_plus_signed_source_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (F : Ω → Finset ℝ≥0)
    (hF : ∀ ω t, t ∈ F ω →
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (A : Ω → ℝ) (hAI : Integrable A P)
    (hAMean : (∫ ω, A ω ∂P) ≤ 0)
    (hAtomInt : Integrable (fun ω =>
      ∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω))) P) :
    Integrable (fun ω => A ω +
      (∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω)))) P ∧
    (∫ ω, A ω +
      (∑ t ∈ F ω, Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) -
          w (riskProcess X x D t ω))) ∂P) ≤ 0 := by sorry
