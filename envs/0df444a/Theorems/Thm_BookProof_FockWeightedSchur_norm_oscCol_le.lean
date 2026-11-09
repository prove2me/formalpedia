-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_norm_oscCol_le
-- name    : BookProof.FockWeightedSchur.norm_oscCol_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:31:57.9978+00:00
-- url     : https://prove2.me/theorems/b9f4fd00-70e8-4cb4-bfd8-02717a2d8c2c
-- title:
--   `BookProof.FockWeightedSchur.norm_oscCol_le` (k j : ℕ) : ‖(oscCol k) j‖ ≤ oscW k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.norm_oscCol_le` (k j : ℕ) : ‖(oscCol k) j‖ ≤ oscW k
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.norm_oscCol_le`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.norm_oscCol_le
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

theorem BookProof.FockWeightedSchur.norm_oscCol_le (k j : ℕ) : ‖(oscCol k) j‖ ≤ oscW k := by sorry
