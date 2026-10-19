-- Prove2me | Theorems.Thm_BookProof_ChapterA_Jmap_mem_of_mem_JY
-- name    : BookProof.ChapterA.Jmap_mem_of_mem_JY
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:53:08.874992+00:00
-- url     : https://prove2.me/theorems/69c8468c-b0e4-43ae-98a4-8df0421b95a7
-- title:
--   `BookProof.ChapterA.Jmap_mem_of_mem_JY` {Y : Submodule ℝ V} {x : V} (hx : x ∈ JY Y) : Jmap x ∈ Y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1e`.
--
--   `BookProof.ChapterA.Jmap_mem_of_mem_JY` {Y : Submodule ℝ V} {x : V} (hx : x ∈ JY Y) : Jmap x ∈ Y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Jmap_mem_of_mem_JY`.

-- Generated from ChapterA1e.lean — theorem BookProof.ChapterA.Jmap_mem_of_mem_JY
import Mathlib
import Definitions.Def_ChapterA1e
import Definitions.Def_ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.Jmap_mem_of_mem_JY {Y : Submodule ℝ V} {x : V} (hx : x ∈ JY Y) : Jmap x ∈ Y := by sorry
