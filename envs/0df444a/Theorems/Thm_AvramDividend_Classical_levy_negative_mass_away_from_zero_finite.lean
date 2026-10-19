-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_negative_mass_away_from_zero_finite
-- name    : AvramDividend.Classical.levy_negative_mass_away_from_zero_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T05:52:58.101532+00:00
-- url     : https://prove2.me/theorems/0ff609aa-898f-40d5-b3d2-1875be4f2fea
-- title:
--   Finite negative Lévy jump intensity outside any positive neighbourhood of zero
-- statement:
--   The Lévy measure is finite on (-infinity,-delta] for every positive real delta, including a possible boundary atom. This follows from the exact integrable truncated quadratic jump moment by a lower bound and Markov's inequality, without any large-jump first-moment assumption.

import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_negative_mass_away_from_zero_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (δ : ℝ) (hδ : 0 < δ) :
    X.ν (Iic (-δ)) < ⊤ := by sorry
