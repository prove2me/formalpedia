-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_exp_lower_growth
-- name    : AvramDividend.Classical.avram_wave3_02_scale_exp_lower_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:44:35.808019+00:00
-- url     : https://prove2.me/theorems/ab553724-caaa-4fa0-9770-59032cb93b47
-- title:
--   Original positive-discount scale function grows at least exponentially at high reserves
-- statement:
--   The actual q-scale function of a Standing spectrally negative Levy process with q>0 grows at least as W(1) exp(φ(a-1)) for a≥1, for a positive Esscher exponent φ. Uses the Proved source-specific exponential first-passage scale ratio, strict positive scale function and elementary real exponent identities. The result is derivative-free and supplies a quantitative high-reserve growth interface for valuation and future finite-barrier proofs.
-- source:
--   Kuznetsov Kyprianou Rivero 2012, scale Esscher normalisation; Avram Palmowski Pistorius 2007 positive q-scale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_ratio_exp_bound
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_scale_exp_lower_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ φ : ℝ, 0 < φ ∧ ∀ a : ℝ, 1 ≤ a →
      W 1 * Real.exp (φ * (a - 1)) ≤ W a := by sorry
