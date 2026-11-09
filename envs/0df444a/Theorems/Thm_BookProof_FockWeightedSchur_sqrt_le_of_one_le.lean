-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_sqrt_le_of_one_le
-- name    : BookProof.FockWeightedSchur.sqrt_le_of_one_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-08T09:28:06.515945+00:00
-- url     : https://prove2.me/theorems/b9843175-0d41-46d6-a60e-9f9db1a56314
-- title:
--   `BookProof.FockWeightedSchur.sqrt_le_of_one_le` {a : ℝ} (h : 1 ≤ a) : Real.sqrt a ≤ a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.sqrt_le_of_one_le` {a : ℝ} (h : 1 ≤ a) : Real.sqrt a ≤ a
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.sqrt_le_of_one_le`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.sqrt_le_of_one_le
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

theorem BookProof.FockWeightedSchur.sqrt_le_of_one_le {a : ℝ} (h : 1 ≤ a) : Real.sqrt a ≤ a := by sorry
