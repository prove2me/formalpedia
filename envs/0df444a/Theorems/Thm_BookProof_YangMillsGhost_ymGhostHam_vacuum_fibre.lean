-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_vacuum_fibre
-- name    : BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:14:34.815989+00:00
-- url     : https://prove2.me/theorems/2479c6c5-2bbf-492b-9ad6-1f3aadee8332
-- title:
--   The Lean 4 theorem `ymGhostHam_vacuum_fibre` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ymGhostHam_vacuum_fibre` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre
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

set_option maxHeartbeats 1000000 in
-- the direct-sum coercions of `lp` over the ghost configurations make the defeq checks here
-- expensive

theorem BookProof.YangMillsGhost.ymGhostHam_vacuum_fibre (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ)
    (x : ghostCore K) :
    ((ymGhostHam fabc ω x : GhostSpace K) : ∀ _ : GConf K, L2d 99) ∅
      = ymHamiltonian (coreRepPoly 99) fabc ⟨(x : GhostSpace K) ∅, x.2.2 ∅⟩ := by sorry
