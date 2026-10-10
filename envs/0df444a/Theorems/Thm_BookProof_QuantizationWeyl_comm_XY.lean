-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_comm_XY
-- name    : BookProof.QuantizationWeyl.comm_XY
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:34:12.912347+00:00
-- url     : https://prove2.me/theorems/7cea6d5e-d897-4f6b-9a27-66a25e3c1a1f
-- title:
--   `BookProof.QuantizationWeyl.comm_XY` : Xgen * Ygen - Ygen * Xgen = Zgen
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.comm_XY` : Xgen * Ygen - Ygen * Xgen = Zgen
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.comm_XY`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.comm_XY
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.comm_XY : Xgen * Ygen - Ygen * Xgen = Zgen := by sorry
