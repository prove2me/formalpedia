-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wRow_oscCol
-- name    : BookProof.FockWeightedSchur.wRow_oscCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:33:07.929078+00:00
-- url     : https://prove2.me/theorems/8c0158e4-9695-495e-9f5c-6ea8c74df915
-- title:
--   `BookProof.FockWeightedSchur.wRow_oscCol` : WRowBound oscW oscCol 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wRow_oscCol` : WRowBound oscW oscCol 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wRow_oscCol`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wRow_oscCol
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

theorem BookProof.FockWeightedSchur.wRow_oscCol : WRowBound oscW oscCol 2 := by sorry
