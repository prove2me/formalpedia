-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ghostEnergy_empty
-- name    : BookProof.YangMillsGhost.ghostEnergy_empty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:51.353862+00:00
-- url     : https://prove2.me/theorems/b7385619-e3ce-46e8-8769-e24f8d2aede5
-- title:
--   The Lean 4 theorem `ghostEnergy_empty` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ghostEnergy_empty` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ghostEnergy_empty
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

theorem BookProof.YangMillsGhost.ghostEnergy_empty (ω : Fin K → ℝ) : ghostEnergy ω (∅ : GConf K) = 0 := by sorry
