-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_dsOp_semibounded
-- name    : BookProof.BddBelowFiberSumEsa.dsOp_semibounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:46:16.935197+00:00
-- url     : https://prove2.me/theorems/5d11504c-8e51-4a77-9da9-6702516d8c71
-- title:
--   The Lean 4 theorem `dsOp_semibounded` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `dsOp_semibounded` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.dsOp_semibounded
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronWallEsa
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterWallEsaSemibounded
open BookProof.DirectSumEsa
open BookProof.WallEsaSemibounded
open BookProof.BddBelowFiberSumEsa

variable {ι : Type*}



open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

theorem BookProof.BddBelowFiberSumEsa.dsOp_semibounded {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}
    (H : ∀ i, D i →ₗ[ℂ] G i) {c : ℝ} (h : ∀ i, SemiboundedBelowOn (D i) (H i) c) :
    SemiboundedBelowOn (dsCore D) (dsOp H) c := by sorry
