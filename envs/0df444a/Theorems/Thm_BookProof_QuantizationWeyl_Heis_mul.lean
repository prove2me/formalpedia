-- Prove2me | Theorems.Thm_BookProof_QuantizationWeyl_Heis_mul
-- name    : BookProof.QuantizationWeyl.Heis_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:34:28.342558+00:00
-- url     : https://prove2.me/theorems/24a08683-4473-466c-9445-3d6efee9413f
-- title:
--   `BookProof.QuantizationWeyl.Heis_mul` (a b c a' b' c' : ℝ) : Heis a b c * Heis a' b' c' = Heis (a + a') (b + b') (c + c' + a * b')
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantizationWeyl`.
--
--   `BookProof.QuantizationWeyl.Heis_mul` (a b c a' b' c' : ℝ) : Heis a b c * Heis a' b' c' = Heis (a + a') (b + b') (c + c' + a * b')
--
--   Formalization note: Lean 4 identifier `BookProof.QuantizationWeyl.Heis_mul`.

-- Generated from ChapterQuantizationWeyl.lean — theorem BookProof.QuantizationWeyl.Heis_mul
import Mathlib
import Definitions.Def_ChapterQuantizationWeyl
open BookProof.QuantizationWeyl


open NormedSpace
open scoped Matrix


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem BookProof.QuantizationWeyl.Heis_mul (a b c a' b' c' : ℝ) :
    Heis a b c * Heis a' b' c' = Heis (a + a') (b + b') (c + c' + a * b') := by sorry
