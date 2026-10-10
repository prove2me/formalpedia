-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_Ngen_sq
-- name    : BookProof.QuantizationWeyl.Ngen_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:34:14.632154+00:00
-- url     : https://prove2.me/theorems/ade1e213-1b4e-48b6-850e-006d01f78b16
-- title:
--   `BookProof.QuantizationWeyl.Ngen_sq` (a b c : ℝ) : (Ngen a b c) ^ 2 = (a * b) • Zgen
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.Ngen_sq` (a b c : ℝ) : (Ngen a b c) ^ 2 = (a * b) • Zgen
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.Ngen_sq`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.Ngen_sq
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.Ngen_sq (a b c : ℝ) : (Ngen a b c) ^ 2 = (a * b) • Zgen := by sorry
