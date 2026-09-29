-- Prove2me | Theorems.Thm_BookProof_YangMillsGhost_ymGhostHam_add_bounded_coupling_esa
-- name    : BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-09-18T01:15:55.080783+00:00
-- url     : https://prove2.me/theorems/4177bc9a-7733-45f8-89ac-ea0d4d1f7926
-- title:
--   The Lean 4 theorem `ymGhostHam_add_bounded_coupling_esa` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `ymGhostHam_add_bounded_coupling_esa` in the `ChapterYangMillsGhostSector` chapter of the timepiece formalization.
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
-- Generated from ChapterYangMillsGhostSector.lean — theorem BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa
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

theorem BookProof.YangMillsGhost.ymGhostHam_add_bounded_coupling_esa (ω : Fin K → ℝ)
    (B : GhostSpace K →L[ℂ] GhostSpace K)
    (hB : ∀ x y : GhostSpace K, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn (ghostCore K)
      (ymGhostHam 0 ω + (B.toLinearMap ∘ₗ (ghostCore K).subtype)) := by sorry
