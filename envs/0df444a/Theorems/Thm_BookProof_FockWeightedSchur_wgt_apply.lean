-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wgt_apply
-- name    : BookProof.FockWeightedSchur.wgt_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:25:04.886659+00:00
-- url     : https://prove2.me/theorems/ed9991aa-f21f-4134-8a89-327bc7f6a945
-- title:
--   `BookProof.FockWeightedSchur.wgt_apply` (u : FockAlg) (α : Conf) : wgt w u α = (wSym w α : ℂ) * u α
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wgt_apply` (u : FockAlg) (α : Conf) : wgt w u α = (wSym w α : ℂ) * u α
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wgt_apply`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wgt_apply
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

theorem BookProof.FockWeightedSchur.wgt_apply (u : FockAlg) (α : Conf) : wgt w u α = (wSym w α : ℂ) * u α := by sorry
