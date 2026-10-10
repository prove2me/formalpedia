-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_exp_Ngen
-- name    : BookProof.QuantizationWeyl.exp_Ngen
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:35:12.749121+00:00
-- url     : https://prove2.me/theorems/849e7984-6980-475f-81e9-411886bd6e44
-- title:
--   `BookProof.QuantizationWeyl.exp_Ngen` (a b c : ℝ) : NormedSpace.exp (Ngen a b c) = Heis a b (c + a * b / 2)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.exp_Ngen` (a b c : ℝ) : NormedSpace.exp (Ngen a b c) = Heis a b (c + a * b / 2)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.exp_Ngen`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.exp_Ngen
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.exp_Ngen (a b c : ℝ) :
    NormedSpace.exp (Ngen a b c) = Heis a b (c + a * b / 2) := by sorry
