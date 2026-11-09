-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_oscCol_not_schurBound
-- name    : BookProof.FockWeightedSchur.oscCol_not_schurBound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T10:46:47.976336+00:00
-- url     : https://prove2.me/theorems/eb7c1936-674e-4021-8a1f-fd6a7d08662d
-- title:
--   `BookProof.FockWeightedSchur.oscCol_not_schurBound` (K : ℝ) : ¬ SchurBound oscCol K
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.oscCol_not_schurBound` (K : ℝ) : ¬ SchurBound oscCol K
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.oscCol_not_schurBound`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.oscCol_not_schurBound
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

theorem BookProof.FockWeightedSchur.oscCol_not_schurBound (K : ℝ) : ¬ SchurBound oscCol K := by sorry
