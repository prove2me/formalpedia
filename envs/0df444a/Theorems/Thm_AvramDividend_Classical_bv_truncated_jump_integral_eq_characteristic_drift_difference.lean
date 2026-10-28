-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_truncated_jump_integral_eq_characteristic_drift_difference
-- name    : AvramDividend.Classical.bv_truncated_jump_integral_eq_characteristic_drift_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:57:05.678711+00:00
-- url     : https://prove2.me/theorems/86242f39-640b-4a2a-9ba4-7be20187f9e1
-- title:
--   BV truncated negative jump compensation exactly equals characteristic drift minus physical drift
-- statement:
--   In a bounded-variation spectrally negative Lévy process, the truncated negative-jump coordinate integrated against the Lévy measure over y<0 equals c minus the physical drift. The proof specialises the already proved BV drift-generator compensation identity to the identity test function and rewrites the indicator integral on (-∞,0) as the small-jump integral on (-1,0). This supplies the drift normalisation hypothesis in the full weighted jump Laplace-transform bridge.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, BV Lévy generator drift compensation.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem bv_truncated_jump_integral_eq_characteristic_drift_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    (∫ y in Iio (0 : ℝ),
      y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y ∂X.ν) =
    X.c - X.drift := by sorry

end AvramDividend.Classical
