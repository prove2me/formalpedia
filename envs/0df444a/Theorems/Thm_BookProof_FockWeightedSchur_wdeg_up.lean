-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wdeg_up
-- name    : BookProof.FockWeightedSchur.wdeg_up
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:24:35.94669+00:00
-- url     : https://prove2.me/theorems/57fb6c2f-c38f-4bc9-b37d-9a177e98e625
-- title:
--   `BookProof.FockWeightedSchur.wdeg_up` (j : ℕ) (α : Conf) : wdeg w (up j α) = wdeg w α + w j ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wdeg_up` (j : ℕ) (α : Conf) : wdeg w (up j α) = wdeg w α + w j ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wdeg_up`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wdeg_up
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}

theorem BookProof.FockWeightedSchur.wdeg_up (j : ℕ) (α : Conf) : wdeg w (up j α) = wdeg w α + w j ^ 2 := by sorry
