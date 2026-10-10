-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_smul_neg_Xgen
-- name    : BookProof.QuantizationWeyl.smul_neg_Xgen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:34:46.317001+00:00
-- url     : https://prove2.me/theorems/97c3fea1-05b3-46e4-8ea8-8e69d937724e
-- title:
--   `BookProof.QuantizationWeyl.smul_neg_Xgen` (a : ℝ) : -(a • Xgen) = Ngen (-a) 0 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.smul_neg_Xgen` (a : ℝ) : -(a • Xgen) = Ngen (-a) 0 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.smul_neg_Xgen`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.smul_neg_Xgen
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.smul_neg_Xgen (a : ℝ) : -(a • Xgen) = Ngen (-a) 0 0 := by sorry
