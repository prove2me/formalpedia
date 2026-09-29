-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_fibreHam_apply
-- name    : BookProof.YangMillsGhost.fibreHam_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:12:39.91739+00:00
-- url     : https://prove2.me/theorems/e80044ec-84b9-47d1-8d70-4bbfd9173848
-- title:
--   The Lean 4 theorem `fibreHam_apply` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `fibreHam_apply` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.fibreHam_apply
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

theorem BookProof.YangMillsGhost.fibreHam_apply (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ) (S : GConf K)
    (x : polyGaussCore (d := 99)) :
    fibreHam fabc ω S x
      = ymHamiltonian (coreRepPoly 99) fabc x + ((ghostEnergy ω S : ℝ) : ℂ) • (x : L2d 99) := by sorry
