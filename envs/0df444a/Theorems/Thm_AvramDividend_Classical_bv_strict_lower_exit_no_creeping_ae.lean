-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_strict_lower_exit_no_creeping_ae
-- name    : AvramDividend.Classical.bv_strict_lower_exit_no_creeping_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:58:38.95081+00:00
-- url     : https://prove2.me/theorems/43a28d8e-14f3-44d6-8b46-347138818c52
-- title:
--   Bounded-variation strict lower exit has a.e. no exact-boundary contact
-- statement:
--   For a standing spectrally negative Levy process with bounded variation, the strict lower two-sided exit (raw iInf form, matching the BV stopped-scale balance parent) has almost surely no exact-boundary contact: on lower-first exit the terminal reserve is not zero. This discharges the explicit a.e. no-creeping hypothesis required by the proved lower-exit vanishing theorem, leaving the stopped martingale identification as the remaining bridge to the BV stopped-scale balance.
-- source:
--   Parent 2bb529c8-d611-4c49-9460-1d4af4620ae8 (Open, BV stopped-scale balance, raw iInf form); Proved chat04_lower_exit_lintegral_zero_of_ae_no_creeping (362ed18d) requires exactly this a.e. hypothesis (named-def form); Proved standing_levy_regular_cases (f5ce6b06) gives 0 < drift and absolutely continuous jump measure from Standing+BV.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_strict_lower_exit_no_creeping_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    ∀ᵐ ω ∂P,
      (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) <
        ⨅ (t : ℝ≥0) (_ : a - x < X.X t ω), (t : ℝ≥0∞) →
      x + X.X (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)).toNNReal ω ≠ 0 := by sorry
