-- Prove2me | Theorems.Thm_BookProof_ChapterG3_mehler_uniform_concentrates
-- name    : BookProof.ChapterG3.mehler_uniform_concentrates
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T13:53:08.519096+00:00
-- url     : https://prove2.me/theorems/9a169192-3e55-4010-9144-fa75a5d230f0
-- title:
--   `BookProof.ChapterG3.mehler_uniform_concentrates` (k : ℕ) (hk : 0 < k) : PhysHSGaussian.sphereUniform k {x | ‖x‖ = Real.sqrt k} = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG3`.
--
--   `BookProof.ChapterG3.mehler_uniform_concentrates` (k : ℕ) (hk : 0 < k) : PhysHSGaussian.sphereUniform k {x | ‖x‖ = Real.sqrt k} = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG3.mehler_uniform_concentrates`.

-- Generated from ChapterG3.lean — theorem BookProof.ChapterG3.mehler_uniform_concentrates
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterG3Promoted
open BookProof.ChapterG3


open MeasureTheory
open scoped ENNReal



variable {X : Type*}

theorem BookProof.ChapterG3.mehler_uniform_concentrates (k : ℕ) (hk : 0 < k) :
    PhysHSGaussian.sphereUniform k {x | ‖x‖ = Real.sqrt k} = 1 := by sorry
