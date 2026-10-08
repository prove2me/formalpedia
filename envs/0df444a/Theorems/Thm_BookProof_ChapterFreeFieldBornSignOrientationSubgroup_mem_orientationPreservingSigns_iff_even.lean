-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationSubgroup_mem_orientationPreservingSigns_iff_even
-- name    : BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T03:58:28.862792+00:00
-- url     : https://prove2.me/theorems/ade1dcd6-8221-4e3f-8cfb-8d312816f35f
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even` (b : Fin n → Bool) : b ∈ orientationPreservingSigns n ↔ Even (flipCount b)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationSubgroup`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even` (b : Fin n → Bool) : b ∈ orientationPreservingSigns n ↔ Even (flipCount b)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even`.

-- Generated from ChapterFreeFieldBornSignOrientationSubgroup.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even
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

theorem BookProof.ChapterFreeFieldBornSignOrientationSubgroup.mem_orientationPreservingSigns_iff_even (b : Fin n → Bool) :
    b ∈ orientationPreservingSigns n ↔ Even (flipCount b) := by sorry
