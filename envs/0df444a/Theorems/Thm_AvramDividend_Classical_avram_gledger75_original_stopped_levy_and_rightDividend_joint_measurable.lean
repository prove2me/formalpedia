-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
-- name    : AvramDividend.Classical.avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:56:11.497285+00:00
-- url     : https://prove2.me/theorems/86eedb7d-a59c-494a-b306-f8d84835415b
-- title:
--   Original right-continuous stopped Lévy and postpayment dividend values are jointly measurable
-- statement:
--   For the same original Lévy process, probability space and right-continuous filtration, original Lévy values and true dividend rightLimits evaluated at every deterministic clipping of a finite stopping time are measurable. This is the missing physical-coordinate part of root-connected gledger71.
-- source:
--   Root-connected gledger71, gledger68, gledger53.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger75_original_stopped_levy_and_rightDividend_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (Δ : ℝ≥0) :
    ∀ i : ℕ,
      Measurable (fun ω => X.X (min ((i : ℝ≥0) * Δ) (ρ ω)) ω) ∧
      Measurable (fun ω => rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω) := by sorry
