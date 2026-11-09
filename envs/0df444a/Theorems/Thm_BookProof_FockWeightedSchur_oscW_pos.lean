-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_oscW_pos
-- name    : BookProof.FockWeightedSchur.oscW_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:30:17.256292+00:00
-- url     : https://prove2.me/theorems/aa4b98e3-f9c7-4c19-8d0c-f0aac2bdb651
-- title:
--   `BookProof.FockWeightedSchur.oscW_pos` (k : ℕ) : 0 < oscW k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.oscW_pos` (k : ℕ) : 0 < oscW k
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.oscW_pos`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.oscW_pos
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

theorem BookProof.FockWeightedSchur.oscW_pos (k : ℕ) : 0 < oscW k := by sorry
