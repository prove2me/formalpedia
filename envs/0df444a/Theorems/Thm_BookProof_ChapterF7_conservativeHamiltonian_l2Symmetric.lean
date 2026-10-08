-- Prove2me | Theorems.Thm_BookProof_ChapterF7_conservativeHamiltonian_l2Symmetric
-- name    : BookProof.ChapterF7.conservativeHamiltonian_l2Symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:07:36.912454+00:00
-- url     : https://prove2.me/theorems/5448226a-6277-45c2-9bca-8e17801deecc
-- title:
--   `BookProof.ChapterF7.conservativeHamiltonian_l2Symmetric` (V : ℝ → ℝ) (hV : Function.HasTemperateGrowth (fun x => (V x : ℂ))) : IsL2Symmetric (Complex.I • (kinetic.comp (mulOp V hV
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.conservativeHamiltonian_l2Symmetric` (V : ℝ → ℝ) (hV : Function.HasTemperateGrowth (fun x => (V x : ℂ))) : IsL2Symmetric (Complex.I • (kinetic.comp (mulOp V hV) - (mulOp V hV).comp kinetic))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.conservativeHamiltonian_l2Symmetric`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.conservativeHamiltonian_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.conservativeHamiltonian_l2Symmetric (V : ℝ → ℝ)
    (hV : Function.HasTemperateGrowth (fun x => (V x : ℂ))) :
    IsL2Symmetric (Complex.I • (kinetic.comp (mulOp V hV) - (mulOp V hV).comp kinetic)) := by sorry
