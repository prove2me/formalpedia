-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_sum_le_of_vanishing
-- name    : BookProof.FockWeightedSchur.sum_le_of_vanishing
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:26:52.063255+00:00
-- url     : https://prove2.me/theorems/acce3cb9-c9ff-4e1e-bc3c-dcf5091cfce3
-- title:
--   `BookProof.FockWeightedSchur.sum_le_of_vanishing` {f : ℕ → ℝ} {S L : Finset ℕ} (hf : ∀ j, 0 ≤ f j) (hz : ∀ j, j ∉ S → f j = 0) : ∑ j ∈ L, f j ≤ ∑ j ∈ S, f j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.sum_le_of_vanishing` {f : ℕ → ℝ} {S L : Finset ℕ} (hf : ∀ j, 0 ≤ f j) (hz : ∀ j, j ∉ S → f j = 0) : ∑ j ∈ L, f j ≤ ∑ j ∈ S, f j
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.sum_le_of_vanishing`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.sum_le_of_vanishing
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

theorem BookProof.FockWeightedSchur.sum_le_of_vanishing {f : ℕ → ℝ} {S L : Finset ℕ} (hf : ∀ j, 0 ≤ f j)
    (hz : ∀ j, j ∉ S → f j = 0) : ∑ j ∈ L, f j ≤ ∑ j ∈ S, f j := by sorry
