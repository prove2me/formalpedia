-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
-- name    : AvramDividend.Classical.chat03_scale_function_borel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:24:50.449272+00:00
-- url     : https://prove2.me/theorems/45cbe3b4-374d-4fa4-b988-e09f93b74cab
-- title:
--   Canonical q-scale function is Borel measurable even when discontinuous at zero
-- statement:
--   For any spectrally negative Lévy process, real q and its official IsScaleFunction X q W, the scale function W is Borel measurable on the entire real line. The canonical scale definition requires continuity only on the nonnegative half-line and W(y)=0 for y<0. Assemble the continuous restriction W on [0,∞) and the constant zero on the negative half-line using the measurable piecewise gluing theorem, without assuming global continuity at 0 (which may fail for bounded-variation Lévy processes). This is a key measurability input for the stopped-scale finite-horizon L² bound and preserves the process's exact hypotheses.
-- source:
--   Exact canonical Formalpedia IsScaleFunction definition at pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, and pinned Mathlib theorem ContinuousOn.measurable_piecewise in MeasureTheory/Constructions/BorelSpace/Basic.levy.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_scale_function_borel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable W := by sorry
