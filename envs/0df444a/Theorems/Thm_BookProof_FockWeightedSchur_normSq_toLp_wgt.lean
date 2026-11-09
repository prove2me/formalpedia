-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_normSq_toLp_wgt
-- name    : BookProof.FockWeightedSchur.normSq_toLp_wgt
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:27:26.947799+00:00
-- url     : https://prove2.me/theorems/1a54d9dd-5a65-4b31-a623-6a61e33fb379
-- title:
--   `BookProof.FockWeightedSchur.normSq_toLp_wgt` (u : FockAlg) : ‖toLp (wgt w u)‖ ^ 2 = ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.normSq_toLp_wgt` (u : FockAlg) : ‖toLp (wgt w u)‖ ^ 2 = ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.normSq_toLp_wgt`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.normSq_toLp_wgt
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
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.normSq_toLp_wgt (u : FockAlg) :
    ‖toLp (wgt w u)‖ ^ 2 = ∑ α ∈ u.support, wSym w α ^ 2 * ‖u α‖ ^ 2 := by sorry
