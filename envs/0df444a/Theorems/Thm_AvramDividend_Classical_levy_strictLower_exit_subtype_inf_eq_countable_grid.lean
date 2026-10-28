-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_strictLower_exit_subtype_inf_eq_countable_grid
-- name    : AvramDividend.Classical.levy_strictLower_exit_subtype_inf_eq_countable_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:47:02.072579+00:00
-- url     : https://prove2.me/theorems/9c8cf4c0-7701-4341-86de-3942142a9bff
-- title:
--   The strict Lévy lower-passage infimum equals its countable inverse-natural grid counterpart
-- statement:
--   For any sample path of an official spectrally negative Lévy process and any lower threshold, the extended first strict downward passage time calculated by infimum over all crossing times equals the infimum over the countably many inverse-natural grid times k/n, n positive. Right-continuity yields finite-horizon grid detection; the accepted generic first-passage infimum extensionality transfers detection to clock equality.
-- source:
--   Proved chat03_lower_before_horizon_countable_grid_iff UUID 0ec8694a-90cc-4e41-9d39-37f4e80426cd and Proved firstPassage_iInf_eq_of_strict_horizon_witness_iff UUID 92726415-3249-44ca-b210-3790cce4b6fe. Lower-side companion to submitted upper strict passage clock equality. Publication repair: pinned Mathlib stores ENNReal under Mathlib.Data.ENNReal.Basic.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_strictLower_exit_subtype_inf_eq_countable_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (lower : ℝ) :
    (⨅ i : {t : ℝ≥0 // X.X t ω < lower}, (i.1 : ℝ≥0∞)) =
      (⨅ j : {p : ℕ × ℕ //
        0 < p.1 ∧
          X.X ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) ω < lower},
        (((j.1.2 : ℝ≥0) * (j.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞)) := by sorry
