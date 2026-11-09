-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wSym_nonneg
-- name    : BookProof.FockWeightedSchur.wSym_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:32.384847+00:00
-- url     : https://prove2.me/theorems/083da3ff-099b-4813-9cce-738f7b1db514
-- title:
--   `BookProof.FockWeightedSchur.wSym_nonneg` (α : Conf) : 0 ≤ wSym w α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wSym_nonneg` (α : Conf) : 0 ≤ wSym w α
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wSym_nonneg`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wSym_nonneg
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

theorem BookProof.FockWeightedSchur.wSym_nonneg (α : Conf) : 0 ≤ wSym w α := by sorry
