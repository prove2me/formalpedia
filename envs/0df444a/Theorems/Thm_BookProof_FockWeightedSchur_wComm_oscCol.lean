-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wComm_oscCol
-- name    : BookProof.FockWeightedSchur.wComm_oscCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:33:08.652687+00:00
-- url     : https://prove2.me/theorems/b833b10d-d4b9-4dce-b32f-a62a30f1b1f4
-- title:
--   `BookProof.FockWeightedSchur.wComm_oscCol` : WCommBound oscW oscCol 4
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wComm_oscCol` : WCommBound oscW oscCol 4
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wComm_oscCol`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wComm_oscCol
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

theorem BookProof.FockWeightedSchur.wComm_oscCol : WCommBound oscW oscCol 4 := by sorry
