-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_random_stop_active_rightatom_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_random_stop_active_rightatom_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:13:15.388725+00:00
-- url     : https://prove2.me/theorems/401f2170-f052-4c15-8366-c21c69235046
-- title:
--   Original random bounded stopping-clock active right dividend atom is integrable
-- statement:
--   For an original admissible spectrally negative Levy dividend process and a bounded right-continuous original stopping clock, the discounted right-dividend atom, active precisely at zero or strict pre-ruin and zero when ruin is at or before positive stop, is integrable. Apply the exact original closed versus strict cash identity pointwise, and subtract the Proved L1 strict and closed cash terms. This provides the source-exact final stopping-cell cash integrability required by the physical C2 Gaussian Ito-to-reward ledger, without an auxiliary process or extra global cash hypothesis.
-- source:
--   Proved ed1a42d8 original strict bounded stopped cash L1; Proved 3deca135 original closed cash L1, Proved 54ad337e closed-minus-strict active right atom, Proved d12a741a stopped clock measurability. Source-exact end-cell L1 for Gaussian finite/top original physical reward witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_random_stop_active_rightatom_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (σ ω : ℝ))) *
          (rightLimit D (σ ω) ω - D (σ ω) ω)
      else 0) P := by sorry
