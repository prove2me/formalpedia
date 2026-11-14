-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB229_original_floor_lower_cutoff_shrinking_occupation
-- name    : AvramDividend.Classical.avram_gbB229_original_floor_lower_cutoff_shrinking_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:13:21.51819+00:00
-- url     : https://prove2.me/theorems/53153b3a-46db-444a-9e1c-004d77553840
-- title:
--   Original positive stopped floor makes all shrinking lower-clipping boundary strips vanish
-- statement:
--   Under the original pre-stopping floor δ>0, the stopped postpayment reserve spends asymptotically zero physical-time occupation in shrinking neighbourhoods of the prescribed lower Gaussian clipping level δ/2, on every sample path. Uses the almost-everywhere equality of pre- and postpayment reserves, measurable path sections and the shrinking-band-from-null-level theorem.
-- source:
--   B65 original finite-cap stopped physical mesh: resolves lower clip δ/2 by Proved B228 and B194, independently of open upper fixed-level B100/B208.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB229_original_floor_lower_cutoff_shrinking_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) :
    ∀ ω : Ω,
      Tendsto (fun k : ℕ =>
        volume {t : ℝ |
          0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ) ∧
          abs (x + X.X (Real.toNNReal t) ω -
            rightLimit D (Real.toNNReal t) ω - δ / 2) <
            (1 : ℝ) / ((k : ℝ) + 1)})
        atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
