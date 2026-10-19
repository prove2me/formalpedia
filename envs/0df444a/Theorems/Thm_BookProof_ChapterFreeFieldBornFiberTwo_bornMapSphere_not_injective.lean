-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornFiberTwo_bornMapSphere_not_injective
-- name    : BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:28:20.930569+00:00
-- url     : https://prove2.me/theorems/657cc246-e140-425e-9e42-74f8aee9c5c3
-- title:
--   `BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective` (hn : 0 < n) : ¬ Function.Injective (bornMapSphere n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornFiberTwo`.
--
--   `BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective` (hn : 0 < n) : ¬ Function.Injective (bornMapSphere n)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective`.

-- Generated from ChapterFreeFieldBornFiberTwo.lean — theorem BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberTwo


open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral


variable {n : ℕ}

theorem BookProof.ChapterFreeFieldBornFiberTwo.bornMapSphere_not_injective (hn : 0 < n) :
    ¬ Function.Injective (bornMapSphere n) := by sorry
