-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_Ngen_eq
-- name    : BookProof.QuantizationWeyl.Ngen_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:34:59.735984+00:00
-- url     : https://prove2.me/theorems/fe1dc56b-4ebb-47bf-90b6-997f24bcbe36
-- title:
--   `BookProof.QuantizationWeyl.Ngen_eq` (a b c : ℝ) : a • Xgen + b • Ygen + c • Zgen = Ngen a b c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.Ngen_eq` (a b c : ℝ) : a • Xgen + b • Ygen + c • Zgen = Ngen a b c
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.Ngen_eq`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.Ngen_eq
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.Ngen_eq (a b c : ℝ) : a • Xgen + b • Ygen + c • Zgen = Ngen a b c := by sorry
