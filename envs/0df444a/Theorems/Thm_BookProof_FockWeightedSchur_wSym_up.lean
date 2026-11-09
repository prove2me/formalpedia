-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wSym_up
-- name    : BookProof.FockWeightedSchur.wSym_up
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:49.369361+00:00
-- url     : https://prove2.me/theorems/8889a5f4-192b-4e52-98f9-c81068af8405
-- title:
--   `BookProof.FockWeightedSchur.wSym_up` (j : ℕ) (α : Conf) : wSym w (up j α) = wSym w α + w j ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wSym_up` (j : ℕ) (α : Conf) : wSym w (up j α) = wSym w α + w j ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wSym_up`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wSym_up
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

theorem BookProof.FockWeightedSchur.wSym_up (j : ℕ) (α : Conf) : wSym w (up j α) = wSym w α + w j ^ 2 := by sorry
