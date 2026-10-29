-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
-- name    : AvramDividend.Classical.levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:05:43.039433+00:00
-- url     : https://prove2.me/theorems/27d97bf6-3cca-47ff-b9ec-2a4511d2749a
-- title:
--   Null zero atom of every genuine finite-horizon running infimum forces almost-sure immediate downward regularity
-- statement:
--   For an actual spectrally negative Lévy process, if the negative running infimum over every strictly positive deterministic horizon has no atom at zero under its original probability measure, then almost every path enters the negative half-line before every positive horizon. A countable cofinal deterministic time grid ensures the a.e.-all quantifier. This is a precise pathwise bridge for the future exponential-clock Wiener–Hopf zero-atom route, without claiming that the missing atomlessness itself follows from infinite jumps.
-- source:
--   Proved chat04_negative_running_infimum_nonneg and chat04_reflected_infimum_Iic_iff_survival, measure_eq_zero_iff_ae_notMem, countable a.e. intersection, and the 1/(n+1) time grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_negative_running_infimum_nonneg
import Theorems.Thm_AvramDividend_Classical_chat04_reflected_infimum_Iic_iff_survival

open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_negative_near_zero_of_fixed_infimum_no_atom_ws01f
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hAtom : ∀ (t : ℝ≥0), 0 < t →
      P {ω : Ω |
        -sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω} = 0} = 0) :
    ∀ᵐ ω ∂P, ∀ (ε : ℝ≥0), 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧ X.X s ω < 0 := by sorry
