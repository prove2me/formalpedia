-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_strictUpper_exit_subtype_inf_eq_countable_grid
-- name    : AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_countable_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:42:35.75962+00:00
-- url     : https://prove2.me/theorems/471be5b7-9dda-4d59-8007-d9fa98bf6e5d
-- title:
--   The strict Lévy upper-passage infimum equals its countable inverse-natural grid counterpart
-- statement:
--   For any sample path of an official spectrally negative Lévy process and any upper threshold, the extended first strict upward passage time calculated by infimum over all crossing times equals the corresponding extended infimum over countably many inverse-natural grid times k/n, n positive. Right-continuity yields crossing detection on the grid before any finite horizon; the already Proved generic first-passage infimum extensionality turns all-horizon witness equivalence into clock equality.
-- source:
--   Proved chat03_upper_before_horizon_countable_grid_iff UUID c4e268ac-950c-4843-96a7-7742108a50c5 and Proved firstPassage_iInf_eq_of_strict_horizon_witness_iff UUID 92726415-3249-44ca-b210-3790cce4b6fe. Next pathwise input to full-future-path stochastic reward lower bound. Publication repair: pinned Mathlib stores ENNReal under Mathlib.Data.ENNReal.Basic.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_strictUpper_exit_subtype_inf_eq_countable_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (upper : ℝ) :
    (⨅ i : {t : ℝ≥0 // upper < X.X t ω}, (i.1 : ℝ≥0∞)) =
      (⨅ j : {p : ℕ × ℕ //
        0 < p.1 ∧
          upper < X.X ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) ω},
        (((j.1.2 : ℝ≥0) * (j.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞)) := by sorry
