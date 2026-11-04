-- Prove2me | Theorems.Thm_BookProof_ChapterG3_mehler_uniform_isProbability
-- name    : BookProof.ChapterG3.mehler_uniform_isProbability
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:34:29.401467+00:00
-- url     : https://prove2.me/theorems/1bfce33f-a292-44e3-913a-85b61fb2c0ce
-- title:
--   `BookProof.ChapterG3.mehler_uniform_isProbability` (k : ℕ) : IsProbabilityMeasure (PhysHSGaussian.sphereUniform k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.mehler_uniform_isProbability` (k : ℕ) : IsProbabilityMeasure (PhysHSGaussian.sphereUniform k)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.mehler_uniform_isProbability`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.mehler_uniform_isProbability
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterG3Promoted
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.mehler_uniform_isProbability (k : ℕ) :
    IsProbabilityMeasure (PhysHSGaussian.sphereUniform k) := by sorry
