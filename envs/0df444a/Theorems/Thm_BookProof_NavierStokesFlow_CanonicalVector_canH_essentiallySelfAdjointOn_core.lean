-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_CanonicalVector_canH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.CanonicalVector.canH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T06:37:23.951792+00:00
-- url     : https://prove2.me/theorems/d1694d4d-5698-478d-b882-013aa19f289b
-- title:
--   canH_essentiallySelfAdjointOn_core
-- statement:
--   Formal statement of `BookProof.NavierStokesFlow.CanonicalVector.canH_essentiallySelfAdjointOn_core` from the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesCanonicalVector.lean`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesCanonicalVector.lean

-- Generated from ChapterNavierStokesCanonicalVector.lean — theorem BookProof.NavierStokesFlow.CanonicalVector.canH_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.CanonicalVector

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ThreeComponent ShiftHamiltonian SignedShift

theorem BookProof.NavierStokesFlow.CanonicalVector.canH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Vel)
      ((lpFiniteModes Vel).subtype.comp (canH A c)) := by sorry
