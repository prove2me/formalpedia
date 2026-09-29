-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ghostCore_dense
-- name    : BookProof.YangMillsGhost.ghostCore_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:54.858505+00:00
-- url     : https://prove2.me/theorems/48aaa840-4fa8-4b5f-8401-5280c066af19
-- title:
--   The Lean 4 theorem `ghostCore_dense` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ghostCore_dense` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ghostCore_dense
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

theorem BookProof.YangMillsGhost.ghostCore_dense : Dense ((ghostCore K : Submodule ℂ (GhostSpace K)) : Set (GhostSpace K)) := by sorry
