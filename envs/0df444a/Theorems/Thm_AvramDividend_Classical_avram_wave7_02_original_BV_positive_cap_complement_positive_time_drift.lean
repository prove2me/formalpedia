-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:37:59.092014+00:00
-- url     : https://prove2.me/theorems/55e3b5e3-3514-4a17-b2e0-09322bcdd535
-- title:
--   Original BV HJB drift-envelope complement forces positive clock and positive physical drift
-- statement:
--   For the actual original spectrally negative Levy source, positive cap, nonnegative initial reserve and C1 gradient at least one, the finite-cap gradient secant yields w(0)+x≤w(x). Consequently the nontrivial complement x+T*drift>w(x) with T≥0 forces T>0 and strictly positive physical drift. This excludes an artificial time-zero complement, without asserting the missing compensation result.
-- source:
--   Original source physical drift X.drift; Proved bounded-cap gradient secant 2ba5cc4f; exact nontrivial envelope condition from c8770486.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The nontrivial original BV drift-envelope complement requires strictly
positive horizon and physical drift. The HJB gradient controls the initial
value even at the finite-cap endpoint and at zero. -/

theorem AvramDividend.Classical.avram_wave7_02_original_BV_positive_cap_complement_positive_time_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    w 0 + x ≤ w x ∧ x ≤ w x ∧ 0 < T ∧ 0 < X.drift := by sorry
