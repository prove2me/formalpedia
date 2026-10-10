-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_smul_Ygen
-- name    : BookProof.QuantizationWeyl.smul_Ygen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:34:29.137732+00:00
-- url     : https://prove2.me/theorems/d6ba2f4f-1c41-4cd2-91af-48dfbb101c1b
-- title:
--   `BookProof.QuantizationWeyl.smul_Ygen` (b : ℝ) : b • Ygen = Ngen 0 b 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.smul_Ygen` (b : ℝ) : b • Ygen = Ngen 0 b 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.smul_Ygen`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.smul_Ygen
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.smul_Ygen (b : ℝ) : b • Ygen = Ngen 0 b 0 := by sorry
