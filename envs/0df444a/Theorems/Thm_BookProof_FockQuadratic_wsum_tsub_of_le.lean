-- Prove2me | Theorems.Thm_BookProof_FockQuadratic_wsum_tsub_of_le
-- name    : BookProof.FockQuadratic.wsum_tsub_of_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:48:43.030106+00:00
-- url     : https://prove2.me/theorems/539843de-9880-4ca5-8a97-649549ab296a
-- title:
--   `BookProof.FockQuadratic.wsum_tsub_of_le` {ω : ι → ℝ} {P a : Idx ι} (h : P ≤ a) : wsum ω (a - P) + wsum ω P = wsum ω a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockQuadraticEsa`.
--
--   `BookProof.FockQuadratic.wsum_tsub_of_le` {ω : ι → ℝ} {P a : Idx ι} (h : P ≤ a) : wsum ω (a - P) + wsum ω P = wsum ω a
--
--   Formalization note: Lean 4 identifier `BookProof.FockQuadratic.wsum_tsub_of_le`.

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.wsum_tsub_of_le
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

theorem BookProof.FockQuadratic.wsum_tsub_of_le {ω : ι → ℝ} {P a : Idx ι} (h : P ≤ a) :
    wsum ω (a - P) + wsum ω P = wsum ω a := by sorry
