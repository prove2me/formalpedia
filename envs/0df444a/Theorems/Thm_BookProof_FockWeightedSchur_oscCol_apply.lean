-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_oscCol_apply
-- name    : BookProof.FockWeightedSchur.oscCol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:29:34.802985+00:00
-- url     : https://prove2.me/theorems/61e1ec02-76b7-4de5-b5a3-7bdbd44e849e
-- title:
--   `BookProof.FockWeightedSchur.oscCol_apply` (k j : ℕ) : (oscCol k) j = if j = k + 1 then ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) else if k = j + 1 then ((Real.sqrt (k : ℝ) : ℝ) : ℂ) els
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.oscCol_apply` (k j : ℕ) : (oscCol k) j = if j = k + 1 then ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ) else if k = j + 1 then ((Real.sqrt (k : ℝ) : ℝ) : ℂ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.oscCol_apply`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.oscCol_apply
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

theorem BookProof.FockWeightedSchur.oscCol_apply (k j : ℕ) : (oscCol k) j =
    if j = k + 1 then ((Real.sqrt ((k : ℝ) + 1) : ℝ) : ℂ)
    else if k = j + 1 then ((Real.sqrt (k : ℝ) : ℝ) : ℂ) else 0 := by sorry
