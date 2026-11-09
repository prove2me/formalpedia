-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_wcomm_nonneg
-- name    : BookProof.FockWeightedSchur.wcomm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:22:36.549255+00:00
-- url     : https://prove2.me/theorems/18bae7d3-385e-48cc-a88b-3095e3a9b7dc
-- title:
--   `BookProof.FockWeightedSchur.wcomm_nonneg` (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) : 0 ≤ B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.wcomm_nonneg` (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) : 0 ≤ B
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.wcomm_nonneg`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.wcomm_nonneg
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

theorem BookProof.FockWeightedSchur.wcomm_nonneg (hw : ∀ k, 1 ≤ w k) (hB : WCommBound w col B) : 0 ≤ B := by sorry
