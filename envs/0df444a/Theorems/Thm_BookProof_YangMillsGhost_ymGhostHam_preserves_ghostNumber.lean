-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_preserves_ghostNumber
-- name    : BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:13:45.796375+00:00
-- url     : https://prove2.me/theorems/4a2a0172-35f0-476b-9d80-2cd2f326d242
-- title:
--   The Lean 4 theorem `ymGhostHam_preserves_ghostNumber` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ymGhostHam_preserves_ghostNumber` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber
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

theorem BookProof.YangMillsGhost.ymGhostHam_preserves_ghostNumber (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ω : Fin K → ℝ)
    (n : ℕ) (x : ghostCore K)
    (hx : ∀ S : GConf K, ghostNum S ≠ n → (x : GhostSpace K) S = 0) :
    ∀ S : GConf K, ghostNum S ≠ n →
      ((ymGhostHam fabc ω x : GhostSpace K) : ∀ _ : GConf K, L2d 99) S = 0 := by sorry
