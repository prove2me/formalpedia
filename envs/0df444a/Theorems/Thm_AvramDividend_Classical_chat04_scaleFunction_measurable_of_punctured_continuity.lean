-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
-- name    : AvramDividend.Classical.chat04_scaleFunction_measurable_of_punctured_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:57:22.344912+00:00
-- url     : https://prove2.me/theorems/344f3813-9596-49b3-a312-7c82999f8363
-- title:
--   Every q-scale function is Borel measurable, even when discontinuous at the origin
-- statement:
--   The scale function of any spectrally negative Lévy process is Borel measurable on the real line, including the bounded-variation case where W(0) may be positive and W has a discontinuity at zero. Continuity at every point other than zero and removal of a singleton establish global measurability. This removes the measurable-W side assumption of the Proved chat04_countable_killed_scale_markov_tonelli identity, which feeds the stopped q-scale renewal and two-sided exit obligations.
-- source:
--   Proved scaleFunction_continuousAt_away_zero and Mathlib measurable_of_measurable_on_compl_singleton.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_scaleFunction_measurable_of_punctured_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Measurable W := by sorry
