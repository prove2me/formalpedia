-- Prove2me | Theorems.Thm_BookProof_DampedOscillatorEnergy_criticallyDamped_hasDerivAt_vel
-- name    : BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:27:17.705431+00:00
-- url     : https://prove2.me/theorems/78026876-ebf4-4018-9eb4-acb0ca8d4b87
-- title:
--   `BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel` (t : ℝ) : HasDerivAt (fun s => -Real.exp (-s)) (Real.exp (-t)) t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDampedOscillatorEnergy`.
--
--   `BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel` (t : ℝ) : HasDerivAt (fun s => -Real.exp (-s)) (Real.exp (-t)) t
--
--   Formalization note: Lean 4 identifier `BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel`.

-- Generated from ChapterDampedOscillatorEnergy.lean — theorem BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy



open MeasureTheory

theorem BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_vel (t : ℝ) :
    HasDerivAt (fun s => -Real.exp (-s)) (Real.exp (-t)) t := by sorry
