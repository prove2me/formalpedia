-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_weyl_shift
-- name    : BookProof.QuantizationWeyl.weyl_shift
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:59.541545+00:00
-- url     : https://prove2.me/theorems/be1b1a90-4a43-493a-9c48-4c291ec442ba
-- title:
--   `BookProof.QuantizationWeyl.weyl_shift` (a b : ℝ) : NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen) * NormedSpace.exp (-(a • Xgen)) = NormedSpace.exp (b • Ygen + (a * b) •
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.weyl_shift` (a b : ℝ) : NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen) * NormedSpace.exp (-(a • Xgen)) = NormedSpace.exp (b • Ygen + (a * b) • Zgen)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.weyl_shift`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.weyl_shift
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.weyl_shift (a b : ℝ) :
    NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen) * NormedSpace.exp (-(a • Xgen))
      = NormedSpace.exp (b • Ygen + (a * b) • Zgen) := by sorry
