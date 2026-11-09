-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_support_oscCol_subset
-- name    : BookProof.FockWeightedSchur.support_oscCol_subset
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:30:53.391094+00:00
-- url     : https://prove2.me/theorems/5a75f7a7-4d8d-4091-b4a5-1b57df647ee5
-- title:
--   `BookProof.FockWeightedSchur.support_oscCol_subset` (k : ℕ) : (oscCol k).support ⊆ {k + 1, k - 1}
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.support_oscCol_subset` (k : ℕ) : (oscCol k).support ⊆ {k + 1, k - 1}
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.support_oscCol_subset`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.support_oscCol_subset
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

theorem BookProof.FockWeightedSchur.support_oscCol_subset (k : ℕ) : (oscCol k).support ⊆ {k + 1, k - 1} := by sorry
