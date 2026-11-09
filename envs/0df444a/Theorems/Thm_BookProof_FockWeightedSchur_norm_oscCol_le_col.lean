-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_le_col
-- name    : BookProof.FockWeightedSchur.norm_oscCol_le_col
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:32:08.718842+00:00
-- url     : https://prove2.me/theorems/4b4f94d2-d5ea-4418-9ad0-e3726bb7bc73
-- title:
--   `BookProof.FockWeightedSchur.norm_oscCol_le_col` (j k : ℕ) : ‖(oscCol j) k‖ ≤ oscW k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.norm_oscCol_le_col` (j k : ℕ) : ‖(oscCol j) k‖ ≤ oscW k
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.norm_oscCol_le_col`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.norm_oscCol_le_col
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

theorem BookProof.FockWeightedSchur.norm_oscCol_le_col (j k : ℕ) : ‖(oscCol j) k‖ ≤ oscW k := by sorry
