-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_fibreHam_abelian_esa
-- name    : BookProof.YangMillsGhost.fibreHam_abelian_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:16.673021+00:00
-- url     : https://prove2.me/theorems/46aac5ab-7c48-456e-b388-bfd66364c7e3
-- title:
--   The Lean 4 theorem `fibreHam_abelian_esa` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fibreHam_abelian_esa` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.fibreHam_abelian_esa
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

theorem BookProof.YangMillsGhost.fibreHam_abelian_esa (ω : Fin K → ℝ) (S : GConf K) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 99)) (fibreHam 0 ω S) := by sorry
