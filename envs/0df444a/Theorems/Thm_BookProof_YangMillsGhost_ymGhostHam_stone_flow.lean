-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_stone_flow
-- name    : BookProof.YangMillsGhost.ymGhostHam_stone_flow
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-18T01:15:38.690985+00:00
-- url     : https://prove2.me/theorems/d116299d-cb21-4c1a-8689-847c7120bbc9
-- title:
--   The Lean 4 theorem `ymGhostHam_stone_flow` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ymGhostHam_stone_flow` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ymGhostHam_stone_flow
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

theorem BookProof.YangMillsGhost.ymGhostHam_stone_flow (ω : Fin K → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (GhostSpace K)) (U : ℝ → (GhostSpace K →L[ℂ] GhostSpace K)),
      IsSelfAdjointExtension (ymGhostHam 0 ω) T.op ∧ IsStoneFlow T U := by sorry
