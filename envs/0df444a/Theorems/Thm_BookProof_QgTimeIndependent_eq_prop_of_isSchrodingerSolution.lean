-- Prove2me | Theorems.Thm_BookProof_QgTimeIndependent_eq_prop_of_isSchrodingerSolution
-- name    : BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-07T23:28:40.405393+00:00
-- url     : https://prove2.me/theorems/60589075-6fa0-4da2-a088-6578bc86f4ca
-- title:
--   `BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution` (T : UnboundedSelfAdjoint E) {y : ℝ → E} (hy : IsSchrodingerSolution T y) (t s : ℝ) : y t = prop T t s (y s)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgTimeIndependentFlow`.
--
--   `BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution` (T : UnboundedSelfAdjoint E) {y : ℝ → E} (hy : IsSchrodingerSolution T y) (t s : ℝ) : y t = prop T t s (y s)
--
--   Formalization note: Lean 4 identifier `BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution`.

-- Generated from ChapterQgTimeIndependentFlow.lean — theorem BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution
import Mathlib
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterAbelianAtomicCondensation
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent
open BookProof.QgTimeIndependent



open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem BookProof.QgTimeIndependent.eq_prop_of_isSchrodingerSolution (T : UnboundedSelfAdjoint E) {y : ℝ → E}
    (hy : IsSchrodingerSolution T y) (t s : ℝ) : y t = prop T t s (y s) := by sorry
