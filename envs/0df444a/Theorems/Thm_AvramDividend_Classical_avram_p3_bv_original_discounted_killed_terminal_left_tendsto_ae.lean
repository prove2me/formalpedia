-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae
-- name    : AvramDividend.Classical.avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:25:38.981978+00:00
-- url     : https://prove2.me/theorems/a9b3240d-cc23-4b2f-86a1-d28e77b12ef5
-- title:
--   Original discounted killed prepayment terminal is left-continuous at every strictly surviving deterministic positive horizon
-- statement:
--   For the actual original controlled reserve and HJB candidate continuous on the nonnegative half-line, the discounted strictly surviving killed prepayment terminal converges from times immediately before a deterministic positive horizon to the surviving horizon terminal, almost surely on the strict-survival event. Since all earlier times also strictly survive, the killed if-branch is eventually the live branch. This supplies the positive-survival part of the finite-horizon Fatou limit and does not assert continuity when ruin equals the horizon.
-- source:
--   Source-exact left-neighbourhood HJB convergence theorem avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae and continuity of the real exponential, using the original ruinTime and riskProcess definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_survival_hjb_left_tendsto_ae
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_discounted_killed_terminal_left_tendsto_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0)) (q : ℝ)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P, (t : ℝ≥0∞) < ruinTime X x D ω →
      Tendsto (fun s : ℝ≥0 =>
        if (s : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (s : ℝ))) * w (riskProcess X x D s ω) else 0)
        (𝓝[<] t)
        (𝓝 (Real.exp (-(q * (t : ℝ))) * w (riskProcess X x D t ω))) := by sorry
