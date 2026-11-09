-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wrow_le
-- name    : BookProof.FockWeightedSchur.wrow_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:26:53.73733+00:00
-- url     : https://prove2.me/theorems/bbf9f54f-2778-48db-95e7-cb5fa07a421b
-- title:
--   `BookProof.FockWeightedSchur.wrow_le` (hw : ∀ k, 1 ≤ w k) (hK : WRowBound w col K) (k : ℕ) (L : Finset ℕ) : ∑ j ∈ L, ‖(col k) j‖ / w k ≤ K
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wrow_le` (hw : ∀ k, 1 ≤ w k) (hK : WRowBound w col K) (k : ℕ) (L : Finset ℕ) : ∑ j ∈ L, ‖(col k) j‖ / w k ≤ K
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wrow_le`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wrow_le
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

theorem BookProof.FockWeightedSchur.wrow_le (hw : ∀ k, 1 ≤ w k) (hK : WRowBound w col K) (k : ℕ) (L : Finset ℕ) :
    ∑ j ∈ L, ‖(col k) j‖ / w k ≤ K := by sorry
