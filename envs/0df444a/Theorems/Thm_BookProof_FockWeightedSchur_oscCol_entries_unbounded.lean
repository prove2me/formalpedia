-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_oscCol_entries_unbounded
-- name    : BookProof.FockWeightedSchur.oscCol_entries_unbounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:33:21.280385+00:00
-- url     : https://prove2.me/theorems/da5b7a6c-1df3-4ed4-b55d-c222cfe496bc
-- title:
--   `BookProof.FockWeightedSchur.oscCol_entries_unbounded` (C : ℝ) : ∃ k : ℕ, C ≤ ‖(oscCol k) (k + 1)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.oscCol_entries_unbounded` (C : ℝ) : ∃ k : ℕ, C ≤ ‖(oscCol k) (k + 1)‖
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.oscCol_entries_unbounded`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.oscCol_entries_unbounded
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

theorem BookProof.FockWeightedSchur.oscCol_entries_unbounded (C : ℝ) : ∃ k : ℕ, C ≤ ‖(oscCol k) (k + 1)‖ := by sorry
