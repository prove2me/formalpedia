-- Prove2me | Theorems.Thm_BookProof_ChapterA_Jmap_mem_JY
-- name    : BookProof.ChapterA.Jmap_mem_JY
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:52:48.091972+00:00
-- url     : https://prove2.me/theorems/3a8de5d9-aed3-43b3-9620-7f7c7d470d2e
-- title:
--   `BookProof.ChapterA.Jmap_mem_JY` {Y : Submodule ℝ V} {y : V} (hy : y ∈ Y) : Jmap y ∈ JY Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1e`.
--
--   `BookProof.ChapterA.Jmap_mem_JY` {Y : Submodule ℝ V} {y : V} (hy : y ∈ Y) : Jmap y ∈ JY Y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Jmap_mem_JY`.

-- Generated from ChapterA1e.lean — theorem BookProof.ChapterA.Jmap_mem_JY
import Mathlib
import Definitions.Def_ChapterA1e
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Jmap_mem_JY {Y : Submodule ℝ V} {y : V} (hy : y ∈ Y) : Jmap y ∈ JY Y := by sorry
