-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite67_original_real_time_cap_strip_joint_measurable
-- name    : AvramDividend.Classical.avram_gfinite67_original_real_time_cap_strip_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:58:57.948672+00:00
-- url     : https://prove2.me/theorems/9fc296da-12be-4d43-84d5-a8988651db13
-- title:
--   Original stopped cap strip is jointly measurable on real time and the original sample space
-- statement:
--   For an original filtered spectrally negative Lévy process and its actual predictable dividend process, every finite right-continuous stopping clock and spatial upper cutoff gives a measurable event in real time times original sample space: t<rho(omega) and cutoff<riskProcess(X,D,Real.toNNReal t,omega). This is the main measurable event prerequisite for inner time integrability and random occupation measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite67_original_real_time_cap_strip_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (b : ℝ) :
    MeasurableSet {z : ℝ × Ω |
      z.1 < (ρ z.2 : ℝ) ∧
        b < riskProcess X x D (Real.toNNReal z.1) z.2} := by
  sorry
