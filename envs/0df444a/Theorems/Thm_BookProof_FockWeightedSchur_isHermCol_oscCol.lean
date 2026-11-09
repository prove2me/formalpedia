-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_isHermCol_oscCol
-- name    : BookProof.FockWeightedSchur.isHermCol_oscCol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T10:19:15.541215+00:00
-- url     : https://prove2.me/theorems/e2b8a2dc-d415-4438-a696-22b5a199ecf4
-- title:
--   `BookProof.FockWeightedSchur.isHermCol_oscCol` : IsHermCol oscCol
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.isHermCol_oscCol` : IsHermCol oscCol
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.isHermCol_oscCol`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.isHermCol_oscCol
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

theorem BookProof.FockWeightedSchur.isHermCol_oscCol : IsHermCol oscCol := by sorry
