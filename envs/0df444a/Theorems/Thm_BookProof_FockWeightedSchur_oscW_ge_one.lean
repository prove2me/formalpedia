-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_oscW_ge_one
-- name    : BookProof.FockWeightedSchur.oscW_ge_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:30:32.394911+00:00
-- url     : https://prove2.me/theorems/c83dabd5-27d2-4ff3-819c-def355491a0c
-- title:
--   `BookProof.FockWeightedSchur.oscW_ge_one` (k : ℕ) : 1 ≤ oscW k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.oscW_ge_one` (k : ℕ) : 1 ≤ oscW k
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.oscW_ge_one`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.oscW_ge_one
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

theorem BookProof.FockWeightedSchur.oscW_ge_one (k : ℕ) : 1 ≤ oscW k := by sorry
