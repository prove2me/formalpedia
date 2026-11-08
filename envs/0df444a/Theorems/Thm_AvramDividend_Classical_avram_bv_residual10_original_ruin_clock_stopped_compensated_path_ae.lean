-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
-- name    : AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:22:18.396115+00:00
-- url     : https://prove2.me/theorems/5d57eb0c-1305-4950-8aa8-75940c09faeb
-- title:
--   Original BV compensated Levy path equals drift at the authentic bounded dividend ruin clock
-- statement:
--   On one common full-measure set of original bounded-variation Levy sample paths, adding the authentic negative-jump sum to the original process at every time stopped by the actual dividend-dependent ruin clock capped at an arbitrary finite S gives drift times stopped physical time. This is a source-exact stochastic stopping interface; it does not make a Brownian equality-in-law substitution, assume any dividend continuity, or alter zero-, ruin- or terminal-time atoms. The stopped finite-grid Taylor and cash budget estimates remain separate tasks.
-- source:
--   AVRAM BV-RESIDUAL10 round 8, stopped original clock, 7 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual10_original_ruin_clock_stopped_compensated_path_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (S : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      X.X (min t τ) ω + J (min t τ) =
        ((min t τ : ℝ≥0) : ℝ) * X.drift := by sorry
