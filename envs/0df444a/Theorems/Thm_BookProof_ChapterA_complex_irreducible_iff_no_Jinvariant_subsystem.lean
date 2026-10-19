-- Prove2me | Theorems.Thm_BookProof_ChapterA_complex_irreducible_iff_no_Jinvariant_subsystem
-- name    : BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:52:01.101563+00:00
-- url     : https://prove2.me/theorems/c0fa0011-30c4-4530-9df9-c4d0e836e99e
-- title:
--   `BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem` [CompleteSpace V] (M : System ℂ V) : M.IsIrreducible ↔ ∀ Y : Submodule ℝ V, (rxSystem M).IsSubsystem Y → (∀ y ∈
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1d`.
--
--   `BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem` [CompleteSpace V] (M : System ℂ V) : M.IsIrreducible ↔ ∀ Y : Submodule ℝ V, (rxSystem M).IsSubsystem Y → (∀ y ∈ Y, Jmap y ∈ Y) → Y = ⊥ ∨ Y = ⊤
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem`.

-- Generated from ChapterA1d.lean — theorem BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem
import Mathlib
import Definitions.Def_ChapterA1d
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterA.complex_irreducible_iff_no_Jinvariant_subsystem [CompleteSpace V] (M : System ℂ V) :
    M.IsIrreducible ↔
      ∀ Y : Submodule ℝ V, (rxSystem M).IsSubsystem Y →
        (∀ y ∈ Y, Jmap y ∈ Y) → Y = ⊥ ∨ Y = ⊤ := by sorry
