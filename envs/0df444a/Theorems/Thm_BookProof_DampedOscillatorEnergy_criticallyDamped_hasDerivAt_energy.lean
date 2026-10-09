-- Prove2me | Theorems.Thm_BookProof_DampedOscillatorEnergy_criticallyDamped_hasDerivAt_energy
-- name    : BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_energy
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:27:08.314864+00:00
-- url     : https://prove2.me/theorems/fbeb0def-1976-402b-8833-f6264a6a8da5
-- title:
--   `BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_energy` (t : ℝ) : HasDerivAt (dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s))) (-(2 * (-Real.exp (-t
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDampedOscillatorEnergy`.
--
--   `BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_energy` (t : ℝ) : HasDerivAt (dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s))) (-(2 * (-Real.exp (-t)) ^ 2)) t
--
--   Formalization note: Lean 4 identifier `BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_energy`.

-- Generated from ChapterDampedOscillatorEnergy.lean — theorem BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_energy
import Mathlib
import Definitions.Def_ChapterDampedOscillatorEnergy
open BookProof.DampedOscillatorEnergy



open MeasureTheory

theorem BookProof.DampedOscillatorEnergy.criticallyDamped_hasDerivAt_energy (t : ℝ) :
    HasDerivAt (dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s)))
      (-(2 * (-Real.exp (-t)) ^ 2)) t := by sorry
