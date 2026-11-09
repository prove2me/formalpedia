-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_apply
-- name    : BookProof.FockWeightedSchur.norm_oscCol_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:28:37.748343+00:00
-- url     : https://prove2.me/theorems/ba875b87-68f9-45a3-ba21-1174902c5ef0
-- title:
--   `BookProof.FockWeightedSchur.norm_oscCol_apply` (k j : ℕ) : ‖(oscCol k) j‖ = if j = k + 1 then Real.sqrt ((k : ℝ) + 1) else if k = j + 1 then Real.sqrt (k : ℝ) else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.norm_oscCol_apply` (k j : ℕ) : ‖(oscCol k) j‖ = if j = k + 1 then Real.sqrt ((k : ℝ) + 1) else if k = j + 1 then Real.sqrt (k : ℝ) else 0
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.norm_oscCol_apply`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.norm_oscCol_apply
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

theorem BookProof.FockWeightedSchur.norm_oscCol_apply (k j : ℕ) : ‖(oscCol k) j‖ =
    if j = k + 1 then Real.sqrt ((k : ℝ) + 1)
    else if k = j + 1 then Real.sqrt (k : ℝ) else 0 := by sorry
