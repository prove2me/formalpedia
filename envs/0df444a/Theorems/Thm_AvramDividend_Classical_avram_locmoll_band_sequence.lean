-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_band_sequence
-- name    : AvramDividend.Classical.avram_locmoll_band_sequence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:02:06.836793+00:00
-- url     : https://prove2.me/theorems/73bc445f-c013-4a83-b0cd-c31e0f9e6648
-- title:
--   Explicit nested positive reserve bands exhaust the positive half-line
-- statement:
--   Explicit nested positive reserve bands exhaust the positive half-line
-- source:
--   Exact decomposition of 1956f1aa-dda2-5052-8723-910f7fb63181, Avram Proposition 4(i)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_band_sequence
    (x η : ℝ) (hx : 0 < x) (hη : 0 < η) :
    ∃ (δ R : ℕ → ℝ),
      (∀ k, 0 < δ k ∧ δ k < x ∧ x < R k) ∧
      (∀ k, δ k ≤ η) ∧ Antitone δ ∧ Monotone R ∧
      Tendsto δ atTop (𝓝 0) ∧ Tendsto R atTop atTop := by sorry
