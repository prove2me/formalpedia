-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wcomm_row_le
-- name    : BookProof.FockWeightedSchur.wcomm_row_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:51.953596+00:00
-- url     : https://prove2.me/theorems/0debad5b-4c1d-4abc-8f7e-efa7856d0665
-- title:
--   `BookProof.FockWeightedSchur.wcomm_row_le` (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) (k : ℕ) (L : Finset ℕ) : ∑ j ∈ L, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wcomm_row_le` (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) (k : ℕ) (L : Finset ℕ) : ∑ j ∈ L, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wcomm_row_le`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wcomm_row_le
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

theorem BookProof.FockWeightedSchur.wcomm_row_le (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) (k : ℕ) (L : Finset ℕ) :
    ∑ j ∈ L, ‖(col k) j‖ * |w j ^ 2 - w k ^ 2| / (w k * w j) ≤ B := by sorry
