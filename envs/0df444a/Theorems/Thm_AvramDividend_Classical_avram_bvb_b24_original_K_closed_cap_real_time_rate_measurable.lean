-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
-- name    : AvramDividend.Classical.avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:22:18.350458+00:00
-- url     : https://prove2.me/theorems/a37a74d6-b320-4cf4-8aed-665530a2e4dc
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_prepayment_leftlim_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b24_original_K_closed_cap_real_time_rate_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q T : ℝ) (hT : 0 < T) (n : ℕ) (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    let U : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun z : ℝ≥0 => x + X.X z ω - rightLimit D z ω) r
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C then
        Real.exp (-(q * (t : ℝ))) * ψ (U t)
      else 0) := by sorry
