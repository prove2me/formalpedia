-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationSubgroup_sub_mem_orientationPreservingSigns_iff
-- name    : BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T03:59:04.416647+00:00
-- url     : https://prove2.me/theorems/b3791712-1e27-4cf7-affe-0927a29b41e8
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff` (b₁ b₂ : Fin n → Bool) : b₁ - b₂ ∈ orientationPreservingSigns n ↔ (b₁ ∈ orientationPr
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationSubgroup`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff` (b₁ b₂ : Fin n → Bool) : b₁ - b₂ ∈ orientationPreservingSigns n ↔ (b₁ ∈ orientationPreservingSigns n ↔ b₂ ∈ orientationPreservingSigns n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff`.

-- Generated from ChapterFreeFieldBornSignOrientationSubgroup.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientationKernel
open BookProof.ChapterFreeFieldBornSignOrientationCard

theorem BookProof.ChapterFreeFieldBornSignOrientationSubgroup.sub_mem_orientationPreservingSigns_iff (b₁ b₂ : Fin n → Bool) :
    b₁ - b₂ ∈ orientationPreservingSigns n ↔
      (b₁ ∈ orientationPreservingSigns n ↔
       b₂ ∈ orientationPreservingSigns n) := by sorry
