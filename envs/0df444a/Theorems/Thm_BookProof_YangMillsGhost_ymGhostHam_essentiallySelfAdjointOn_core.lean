-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_essentiallySelfAdjointOn_core
-- name    : BookProof.YangMillsGhost.ymGhostHam_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:36.609811+00:00
-- url     : https://prove2.me/theorems/9916bc1a-0df8-45f9-bc4e-33f930c21841
-- title:
--   The Lean 4 theorem `ymGhostHam_essentiallySelfAdjointOn_core` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ymGhostHam_essentiallySelfAdjointOn_core` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsGhostSector.lean

import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsAbelianEsa
import Definitions.Def_ChapterYangMillsHermite
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ymGhostHam_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterYangMillsGhostSector
import Definitions.Def_ChapterYangMillsGhostSector
open BookProof.YangMillsGhost














noncomputable section

open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.YangMillsHermite BookProof.YangMillsAbelianEsa
open BookProof.StoneBridge BookProof.EsaClosure
open BookProof.ChapterStoneResolvent

variable {K : ℕ}

theorem BookProof.YangMillsGhost.ymGhostHam_essentiallySelfAdjointOn_core (ω : Fin K → ℝ) :
    EssentiallySelfAdjointOn (ghostCore K) (ymGhostHam 0 ω) := by sorry
