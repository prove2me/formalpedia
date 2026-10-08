-- Prove2me | Theorems.Thm_BookProof_ChapterF7_continuityHamiltonian_l2Symmetric
-- name    : BookProof.ChapterF7.continuityHamiltonian_l2Symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:07:25.439623+00:00
-- url     : https://prove2.me/theorems/18776e07-e0b1-49c2-b0e3-0f618c1bbe35
-- title:
--   `BookProof.ChapterF7.continuityHamiltonian_l2Symmetric` (v : ℝ → ℝ) (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) : IsL2Symmetric (((1 : ℂ) / 2) • (momentum.comp (mulOp v
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.continuityHamiltonian_l2Symmetric` (v : ℝ → ℝ) (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) : IsL2Symmetric (((1 : ℂ) / 2) • (momentum.comp (mulOp v hv) + (mulOp v hv).comp momentum))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.continuityHamiltonian_l2Symmetric`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.continuityHamiltonian_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.continuityHamiltonian_l2Symmetric (v : ℝ → ℝ)
    (hv : Function.HasTemperateGrowth (fun x => (v x : ℂ))) :
    IsL2Symmetric
      (((1 : ℂ) / 2) • (momentum.comp (mulOp v hv) + (mulOp v hv).comp momentum)) := by sorry
