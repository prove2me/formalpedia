-- Prove2me | solution 1 for section5_roundCoord_error
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:23:52.641823+00:00
-- url     : https://prove2.me/submissions/8e7ad0e3-5a32-4b74-be02-9f8039c19a73

import Definitions.Def_QuantumLTF_Example_HermiteModel
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory QuantumLTF.Membership QuantumLTF.Example
theorem solution {M : ℕ} (hM : 1 ≤ M) (x : ℝ) :
    |x-roundCoord M x| ≤ gridSpacing M := by
  have hδ : 0 < gridSpacing M := by
    dsimp [gridSpacing]
    positivity
  let u := (x+gridRadius M)/gridSpacing M
  have hlo := Int.floor_le u
  have hhi := Int.lt_floor_add_one u
  have hu : u*gridSpacing M = x+gridRadius M := by dsimp [u]; field_simp
  have hl := mul_le_mul_of_nonneg_right hlo hδ.le
  have hh := mul_lt_mul_of_pos_right hhi hδ
  change |x-(-gridRadius M+gridSpacing M*(⌊u⌋:ℝ))| ≤ gridSpacing M
  apply abs_le.mpr
  constructor <;> nlinarith
