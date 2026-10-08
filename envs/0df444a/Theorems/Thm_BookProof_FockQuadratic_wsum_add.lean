-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_wsum_add
-- name    : BookProof.FockQuadratic.wsum_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:47:57.845308+00:00
-- url     : https://prove2.me/theorems/34c7ef75-77b9-4468-b95d-a82780f1845f
-- title:
--   `BookProof.FockQuadratic.wsum_add` (ω : ι → ℝ) (a b : Idx ι) : wsum ω (a + b) = wsum ω a + wsum ω b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.wsum_add` (ω : ι → ℝ) (a b : Idx ι) : wsum ω (a + b) = wsum ω a + wsum ω b
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.wsum_add`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.wsum_add
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


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem BookProof.FockQuadratic.wsum_add (ω : ι → ℝ) (a b : Idx ι) : wsum ω (a + b) = wsum ω a + wsum ω b := by sorry
