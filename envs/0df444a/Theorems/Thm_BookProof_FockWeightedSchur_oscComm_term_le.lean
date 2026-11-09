-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_oscComm_term_le
-- name    : BookProof.FockWeightedSchur.oscComm_term_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:32:59.141794+00:00
-- url     : https://prove2.me/theorems/3f9d7a29-0fc4-408b-bf5b-efe7646fae07
-- title:
--   `BookProof.FockWeightedSchur.oscComm_term_le` (k j : ℕ) : ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j) ≤ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.oscComm_term_le` (k j : ℕ) : ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j) ≤ 2
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.oscComm_term_le`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.oscComm_term_le
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

theorem BookProof.FockWeightedSchur.oscComm_term_le (k j : ℕ) :
    ‖(oscCol k) j‖ * |oscW j ^ 2 - oscW k ^ 2| / (oscW k * oscW j) ≤ 2 := by sorry
