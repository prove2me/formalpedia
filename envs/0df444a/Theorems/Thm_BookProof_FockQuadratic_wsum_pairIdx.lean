-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_wsum_pairIdx
-- name    : BookProof.FockQuadratic.wsum_pairIdx
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:17:18.449245+00:00
-- url     : https://prove2.me/theorems/fc4b291e-67d7-4f25-b5b4-be7a7bf6e9d3
-- title:
--   `BookProof.FockQuadratic.wsum_pairIdx` (ω : ι → ℝ) (m n : ι) : wsum ω (pairIdx m n) = ω m + ω n
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.wsum_pairIdx` (ω : ι → ℝ) (m n : ι) : wsum ω (pairIdx m n) = ω m + ω n
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.wsum_pairIdx`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.wsum_pairIdx
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.FockQuadratic

variable {ι : Type*}
variable {ω : ι → ℝ}
variable {κ : Type*}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.wsum_pairIdx (ω : ι → ℝ) (m n : ι) : wsum ω (pairIdx m n) = ω m + ω n := by sorry
