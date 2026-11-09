-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_w_pos
-- name    : BookProof.FockWeightedSchur.w_pos
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:28.199382+00:00
-- url     : https://prove2.me/theorems/8d2e32d5-da90-4a3b-af96-9745f3bed658
-- title:
--   `BookProof.FockWeightedSchur.w_pos` (hw : ∀ k, 1 ≤ w k) (k : ℕ) : 0 < w k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.w_pos` (hw : ∀ k, 1 ≤ w k) (k : ℕ) : 0 < w k
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.w_pos`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.w_pos
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

theorem BookProof.FockWeightedSchur.w_pos (hw : ∀ k, 1 ≤ w k) (k : ℕ) : 0 < w k := by sorry
