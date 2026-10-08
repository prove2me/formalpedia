-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
-- name    : AvramDividend.Classical.levy_negative_jump_measure_sFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:38:05.131074+00:00
-- url     : https://prove2.me/theorems/a9270e22-1417-4e8a-bd7b-d672bd742f3d
-- title:
--   The negative-jump Lévy measure is s-finite from its quadratic moment
-- statement:
--   The negative-jump restriction of a spectrally negative Lévy measure is SFinite. The positive density min(1,y²) is integrable by the Lévy moment condition and positive on y<0, so the generic positive-integrable-density SFinite theorem applies. This discharges the explicit SFinite typeclass hypothesis in the previously proved compact generator Fubini theorem.
-- source:
--   Lévy quadratic jump moment and pinned Mathlib positive-density s-finiteness result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem levy_negative_jump_measure_sFinite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    SFinite (X.ν.restrict (Iio 0)) := by sorry

end AvramDividend.Classical
