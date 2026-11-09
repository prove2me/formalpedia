-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wCol_oscCol
-- name    : BookProof.FockWeightedSchur.wCol_oscCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:32:29.525233+00:00
-- url     : https://prove2.me/theorems/81ab4048-9796-4d9d-a3e8-7012a879da78
-- title:
--   `BookProof.FockWeightedSchur.wCol_oscCol` : WColBound oscW oscCol 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wCol_oscCol` : WColBound oscW oscCol 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wCol_oscCol`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wCol_oscCol
import Definitions.Def_ChapterFockSecondQuantization
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
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.wCol_oscCol : WColBound oscW oscCol 2 := by sorry
