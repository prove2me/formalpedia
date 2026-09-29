-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_symmetricOn
-- name    : BookProof.YangMillsGhost.ymGhostHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:14:48.048149+00:00
-- url     : https://prove2.me/theorems/51cd00a0-d202-4a95-80da-3a8e59983c4e
-- title:
--   The Lean 4 theorem `ymGhostHam_symmetricOn` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ymGhostHam_symmetricOn` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ymGhostHam_symmetricOn
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

theorem BookProof.YangMillsGhost.ymGhostHam_symmetricOn (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ) :
    SymmetricOn (ghostCore K) (ymGhostHam fabc ω) := by sorry
